#!/usr/bin/env bash
# External-client interoperability gate for the tls13-lean server.
#
# Drives the one-shot loopback harness (Test:tls_external_server) with real,
# independently implemented TLS 1.3 clients and asserts that every handshake
# completes and (for HTTP clients) that the HTTP/1.1 200 body arrives:
#
#   1. openssl s_client, default groups (covers tolerance of a hybrid
#      X25519MLKEM768 key share on OpenSSL >= 3.5)     -> X25519
#   2. openssl s_client -groups P-384:X25519 (first-flight share is only
#      P-384, which the server does not implement)     -> HelloRetryRequest
#   3. curl HTTPS GET                                  -> HTTP/1.1 200 "OK"
#   4. curl HTTPS GET against a server reading the transport 7 bytes at a
#      time (record fragmentation/coalescing at arbitrary boundaries)
#   5. go crypto/tls GET, default config (hybrid + X25519 shares)
#   6. go crypto/tls GET restricted to {X25519MLKEM768, P-256} so the only
#      first-flight share is one the server does not implement -> HRR to P-256
#
# openssl and curl are required on PATH. The Go cases are skipped with a
# notice when no `go` binary is available (e.g. run
# `nix shell nixpkgs#go -c bazel test //Test:external_interop_test ...`).
#
# The gate is tagged manual/local: it binds loopback TCP ports and shells out
# to host tools, so it is excluded from the hermetic //... wildcard. Set
# TLS_INTEROP_PORT to pin the first port (each case increments from there);
# by default a random high port is chosen per case.

set -u

FAILURES=0
SERVER_PID=""
SERVER_LOG=""

note() { echo "[interop] $*"; }

fail() {
  echo "[interop] FAIL: $*" >&2
  FAILURES=$((FAILURES + 1))
}

cleanup() {
  if [[ -n "${SERVER_PID}" ]] && kill -0 "${SERVER_PID}" 2>/dev/null; then
    kill "${SERVER_PID}" 2>/dev/null || true
    wait "${SERVER_PID}" 2>/dev/null || true
  fi
}
trap cleanup EXIT

# --- Locate inputs (bazel runfiles first, then a repo-root invocation). ---
runfile() {
  local rel="$1"
  if [[ -n "${TEST_SRCDIR:-}" && -e "${TEST_SRCDIR}/_main/${rel}" ]]; then
    echo "${TEST_SRCDIR}/_main/${rel}"
  elif [[ -e "${rel}" ]]; then
    echo "${rel}"
  elif [[ -e "bazel-bin/${rel}" ]]; then
    echo "bazel-bin/${rel}"
  else
    echo ""
  fi
}

SERVER_BIN="$(runfile Test/tls_external_server)"
CERT="$(runfile Test/Fixtures/Tls/server_cert.pem)"
GO_SRC="$(runfile Test/interop/goclient/main.go)"
[[ -x "${SERVER_BIN}" ]] || { echo "server harness not found" >&2; exit 1; }
[[ -f "${CERT}" ]] || { echo "certificate fixture not found" >&2; exit 1; }
command -v openssl >/dev/null || { echo "openssl not on PATH" >&2; exit 1; }
command -v curl >/dev/null || { echo "curl not on PATH" >&2; exit 1; }

# The harness reads Test/Fixtures/Tls/server_cert.pem relative to its CWD, so
# run it from the directory that contains that relative path (the runfiles
# root under bazel test, the repository root otherwise).
SERVER_BIN="$(cd "$(dirname "${SERVER_BIN}")" && pwd)/$(basename "${SERVER_BIN}")"
CERT="$(cd "$(dirname "${CERT}")" && pwd)/$(basename "${CERT}")"
SERVER_CWD="$(cd "$(dirname "${CERT}")/../../.." && pwd)"
[[ -z "${GO_SRC}" ]] || GO_SRC="$(cd "$(dirname "${GO_SRC}")" && pwd)/$(basename "${GO_SRC}")"

WORK="${TEST_TMPDIR:-$(mktemp -d)}"
mkdir -p "${WORK}"
PORT="${TLS_INTEROP_PORT:-$(( 20000 + RANDOM % 40000 ))}"

# Start one single-connection server instance; echoes nothing, sets
# SERVER_PID/SERVER_LOG, retries on bind failure with the next port.
start_server() {
  local readsize="${1:-}"
  local attempt
  for attempt in 1 2 3 4 5; do
    PORT=$((PORT + 1))
    SERVER_LOG="${WORK}/server-${PORT}.log"
    if [[ -n "${readsize}" ]]; then
      (cd "${SERVER_CWD}" && exec "${SERVER_BIN}" "${PORT}" "${readsize}") \
        >"${SERVER_LOG}" 2>&1 &
    else
      (cd "${SERVER_CWD}" && exec "${SERVER_BIN}" "${PORT}") \
        >"${SERVER_LOG}" 2>&1 &
    fi
    SERVER_PID=$!
    local i
    for i in $(seq 1 50); do
      if grep -q "^READY " "${SERVER_LOG}" 2>/dev/null; then
        return 0
      fi
      if ! kill -0 "${SERVER_PID}" 2>/dev/null; then
        break  # bind failure or crash: retry on the next port
      fi
      sleep 0.1
    done
    kill "${SERVER_PID}" 2>/dev/null || true
    wait "${SERVER_PID}" 2>/dev/null || true
  done
  echo "server harness failed to start; last log:" >&2
  cat "${SERVER_LOG}" >&2 || true
  exit 1
}

# Wait (bounded) for the one-shot server to finish its connection.
finish_server() {
  local i
  for i in $(seq 1 100); do
    kill -0 "${SERVER_PID}" 2>/dev/null || break
    sleep 0.1
  done
  kill "${SERVER_PID}" 2>/dev/null || true
  wait "${SERVER_PID}" 2>/dev/null || true
  SERVER_PID=""
}

server_negotiated() {
  grep -q "^NEGOTIATED " "${SERVER_LOG}"
}

server_saw_hrr() {
  grep -q "waitingSecondClientHello" "${SERVER_LOG}"
}

dump_case() {
  local name="$1" clientlog="$2"
  echo "--- ${name}: server log ---" >&2
  cat "${SERVER_LOG}" >&2 || true
  echo "--- ${name}: client log ---" >&2
  cat "${clientlog}" >&2 || true
}

# --- Case 1: openssl s_client, default groups. ---
run_openssl() {
  local name="$1"; shift
  local log="${WORK}/${name}.log"
  start_server
  timeout 30 openssl s_client -connect "127.0.0.1:${PORT}" -tls1_3 \
    -CAfile "${CERT}" -servername localhost -verify_return_error -brief \
    "$@" </dev/null >"${log}" 2>&1
  local rc=$?
  finish_server
  if [[ ${rc} -ne 0 ]] \
      || ! grep -q "TLS_CHACHA20_POLY1305_SHA256" "${log}" \
      || ! server_negotiated; then
    dump_case "${name}" "${log}"
    fail "${name}: openssl handshake did not complete (rc=${rc})"
    return 1
  fi
  return 0
}

if run_openssl openssl-default; then
  note "PASS openssl default groups ($(grep '^NEGOTIATED' "${SERVER_LOG}"))"
fi

# --- Case 2: openssl forced HelloRetryRequest (share only for P-384). ---
if run_openssl openssl-hrr -groups P-384:X25519; then
  if server_saw_hrr; then
    note "PASS openssl HelloRetryRequest ($(grep '^NEGOTIATED' "${SERVER_LOG}"))"
  else
    dump_case openssl-hrr "${WORK}/openssl-hrr.log"
    fail "openssl-hrr: handshake completed without exercising HelloRetryRequest"
  fi
fi

# --- Case 3/4: curl fetches the page (default and 7-byte transport reads). ---
run_curl() {
  local name="$1" readsize="${2:-}"
  local log="${WORK}/${name}.log"
  start_server "${readsize}"
  local body
  body="$(timeout 30 curl -sS --fail --cacert "${CERT}" \
    --connect-to "localhost:${PORT}:127.0.0.1:${PORT}" \
    "https://localhost:${PORT}/" 2>"${log}")"
  local rc=$?
  finish_server
  if [[ ${rc} -ne 0 || "${body}" != "OK" ]] || ! server_negotiated; then
    dump_case "${name}" "${log}"
    fail "${name}: curl fetch failed (rc=${rc}, body=${body@Q})"
    return 1
  fi
  return 0
}

if run_curl curl-default; then
  note "PASS curl HTTP/1.1 200 ($(grep '^NEGOTIATED' "${SERVER_LOG}"))"
fi
if run_curl curl-fragmented 7; then
  note "PASS curl with 7-byte server transport reads"
fi

# --- Case 5/6: Go crypto/tls (skipped without a go toolchain). ---
if [[ -n "${GO_SRC}" ]] && command -v go >/dev/null; then
  export GOCACHE="${WORK}/gocache" GOPATH="${WORK}/gopath" \
    HOME="${HOME:-${WORK}/home}" GOFLAGS=""
  export GOTOOLCHAIN=local GOPROXY=off
  mkdir -p "${GOCACHE}" "${GOPATH}" "${HOME}"

  run_go() {
    local name="$1"; shift
    local log="${WORK}/${name}.log"
    start_server
    timeout 120 go run "${GO_SRC}" -addr "127.0.0.1:${PORT}" \
      -cafile "${CERT}" "$@" >"${log}" 2>&1
    local rc=$?
    finish_server
    if [[ ${rc} -ne 0 ]] || ! grep -q "^GO-OK" "${log}" \
        || ! server_negotiated; then
      dump_case "${name}" "${log}"
      fail "${name}: Go client failed (rc=${rc})"
      return 1
    fi
    return 0
  }

  if run_go go-default; then
    note "PASS go crypto/tls default ($(grep '^NEGOTIATED' "${SERVER_LOG}"))"
  fi
  if run_go go-hrr -hrr; then
    if server_saw_hrr; then
      note "PASS go crypto/tls HelloRetryRequest ($(grep '^NEGOTIATED' "${SERVER_LOG}"))"
    else
      dump_case go-hrr "${WORK}/go-hrr.log"
      fail "go-hrr: handshake completed without exercising HelloRetryRequest"
    fi
  fi
else
  note "SKIP go crypto/tls cases: no go binary on PATH"
fi

if [[ ${FAILURES} -ne 0 ]]; then
  echo "[interop] ${FAILURES} case(s) failed" >&2
  exit 1
fi
note "all cases passed"
