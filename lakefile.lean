import Lake
open Lake DSL System

package crashproof where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

/-- The verified library: disk model, programs, the log and its proofs. No I/O. -/
@[default_target]
lean_lib Crashproof

/-- The unverified shell around it: block device, crash injection, command line. -/
lean_lib App

input_file dev_c where
  path := "native" / "dev.c"
  text := true

/-- pread/pwrite/fsync for the block device (Lean's standard library has no seek). -/
target dev_o pkg : FilePath := do
  let src ← dev_c.fetch
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "native" / "dev.o") src #["-I", leanInclude.toString]
    #["-O2", "-fPIC", "-Wall"] "cc"

@[default_target]
lean_exe crashproof where
  root := `Main
  moreLinkObjs := #[dev_o]

lean_exe «crashproof-tests» where
  srcDir := "test"
  root := `CrashproofTests
  moreLinkObjs := #[dev_o]
