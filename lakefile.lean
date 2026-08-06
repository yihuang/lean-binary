import Lake
open Lake DSL System

package binary

-- `precompileModules` so the interpreter can reach the native codec below:
-- `Binary.Examples` evaluates it with `#eval` and `native_decide`, and those
-- run at elaboration time, where an `@[extern]` symbol is only available if
-- the module was precompiled into a shared library.
@[default_target]
lean_lib Binary where
  precompileModules := true

-- Not default targets: built on demand.
lean_exe bench where
  root := `Bench

/-- Differential test of the native codec against the specification.
`lake build difftest && ./.lake/build/bin/difftest` -/
lean_exe difftest where
  root := `Difftest

/-! ## the native byte codec (`c/binary_shim.c`)

Lean links GMP but does not ship `gmp.h`, so the one build input this package
cannot find on its own is that header.  The usual prefixes are tried, with
`GMP_INCLUDE_DIR` to override; a clear error beats a hundred lines of
preprocessor output. -/

def gmpIncludeFlags : IO (Array String) := do
  if let some dir ← IO.getEnv "GMP_INCLUDE_DIR" then
    return #["-I", dir]
  for dir in ["/opt/homebrew/include", "/usr/local/include", "/usr/include"] do
    if ← System.FilePath.pathExists (dir / "gmp.h") then
      return #["-I", dir]
  throw <| IO.userError
    "gmp.h not found in the usual prefixes.  Lean links GMP but does not ship \
     its header: install it, or point GMP_INCLUDE_DIR at the directory holding it."

target binary_shim.o pkg : FilePath := do
  let src ← inputTextFile <| pkg.dir / "c" / "binary_shim.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-O2", "-fPIC"] ++ (← gmpIncludeFlags)
  buildO (pkg.buildDir / "c" / "binary_shim.o") src flags

extern_lib libbinaryshim pkg := do
  let o ← binary_shim.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "binaryshim") #[o]
