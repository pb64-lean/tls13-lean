"""Expose the active Lean toolchain's C runtime headers as a CcInfo target.

FFI libraries must compile against the same Lean runtime selected for the
consumer.  Referring to a repository created by this module's own toolchain
extension works only when tls13-lean is the root module: dev-only repositories
are not visible when it is consumed as a dependency.  This tiny adapter reads
the registered toolchain instead, so downstream builds remain hermetic and use
their selected Lean version.
"""

def _toolchain_root(toolchain):
    lean_path = toolchain.lean.path
    if "/bin/lean" in lean_path:
        return lean_path.rsplit("/bin/lean", 1)[0]
    return lean_path.rsplit("/", 1)[0]

def _lean_runtime_headers_impl(ctx):
    toolchain = ctx.toolchains["@rules_lean//lean:toolchain_type"].lean_toolchain
    return [
        CcInfo(
            compilation_context = cc_common.create_compilation_context(
                headers = depset(toolchain.runtime_headers),
                includes = depset([
                    _toolchain_root(toolchain) + "/" + toolchain.lean_include,
                ]),
            ),
        ),
    ]

lean_runtime_headers = rule(
    implementation = _lean_runtime_headers_impl,
    toolchains = ["@rules_lean//lean:toolchain_type"],
    provides = [CcInfo],
)
