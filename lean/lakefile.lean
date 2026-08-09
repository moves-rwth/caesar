import Lake
open Lake DSL

package «caesar» where
  -- add package configuration options here
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

lean_lib «Caesar» where
  -- add library configuration options here

@[default_target]
lean_exe «caesar» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
