/-
  The two variants of the checksum. This file is part of the
  specification: `bar.toml` lists it with `Spec.lean` and
  `Spec/Defs.lean`, and a reviewer approves it with them. The
  statements use the type, and the code returns it.
-/

namespace Bech32

/-- The two checksum variants. -/
inductive Variant where
  /-- BIP 173. -/
  | bech32
  /-- BIP 350. -/
  | bech32m
  deriving DecidableEq, Repr

end Bech32
