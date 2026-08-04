// Minimal Go crypto/tls interop client for the tls13-lean external server
// harness (Test:tls_external_server).
//
// Usage: go run main.go -addr 127.0.0.1:8443 -cafile ../../Fixtures/Tls/server_cert.pem [-hrr]
//
// It dials TLS 1.3 with the fixture certificate as the only root, requires
// ServerName "localhost", sends a GET, and requires an HTTP/1.1 200 response.
// With -hrr it restricts CurvePreferences to {X25519MLKEM768, P-256} so the
// first flight carries only an X25519MLKEM768 key share the server does not
// implement; P-256 remains in supported_groups without a share, forcing the
// server to answer with a HelloRetryRequest and exercising the retry path
// end to end.
package main

import (
	"crypto/tls"
	"crypto/x509"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"
	"time"
)

func main() {
	addr := flag.String("addr", "127.0.0.1:8443", "server address")
	caFile := flag.String("cafile", "Test/Fixtures/Tls/server_cert.pem", "root CA PEM")
	hrr := flag.Bool("hrr", false, "offer no usable first-flight key share to force HelloRetryRequest")
	flag.Parse()

	pem, err := os.ReadFile(*caFile)
	if err != nil {
		fatal("read CA file: %v", err)
	}
	roots := x509.NewCertPool()
	if !roots.AppendCertsFromPEM(pem) {
		fatal("no certificates parsed from %s", *caFile)
	}

	cfg := &tls.Config{
		ServerName: "localhost",
		RootCAs:    roots,
		MinVersion: tls.VersionTLS13,
		NextProtos: []string{"http/1.1"},
	}
	if *hrr {
		// Go orders supported groups by its fixed internal preference and
		// sends a key share only for the first one (plus an X25519 fallback
		// share only when X25519 itself is allowed). Allowing exactly
		// {X25519MLKEM768, P-256} therefore yields a first flight whose only
		// key share is the hybrid one, which the server does not implement;
		// P-256 appears in supported_groups without a share, so the server
		// must answer with a HelloRetryRequest selecting P-256.
		cfg.CurvePreferences = []tls.CurveID{tls.X25519MLKEM768, tls.CurveP256}
	}

	conn, err := tls.Dial("tcp", *addr, cfg)
	if err != nil {
		fatal("dial: %v", err)
	}
	defer conn.Close()
	conn.SetDeadline(time.Now().Add(15 * time.Second))

	state := conn.ConnectionState()
	fmt.Printf("GO-NEGOTIATED version=%x suite=%s alpn=%q\n",
		state.Version, tls.CipherSuiteName(state.CipherSuite), state.NegotiatedProtocol)

	request := "GET / HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"
	if _, err := io.WriteString(conn, request); err != nil {
		fatal("write request: %v", err)
	}
	response, err := io.ReadAll(conn)
	if err != nil {
		fatal("read response: %v", err)
	}
	text := string(response)
	fmt.Printf("GO-RESPONSE %q\n", firstLine(text))
	if !strings.HasPrefix(text, "HTTP/1.1 200") {
		fatal("expected HTTP/1.1 200, got %q", firstLine(text))
	}
	fmt.Println("GO-OK")
}

func firstLine(s string) string {
	if i := strings.IndexByte(s, '\n'); i >= 0 {
		return strings.TrimRight(s[:i], "\r")
	}
	return s
}

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "GO-FAIL "+format+"\n", args...)
	os.Exit(1)
}
