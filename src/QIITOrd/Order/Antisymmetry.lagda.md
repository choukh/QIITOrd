<!-- SPDX-License-Identifier: AGPL-3.0-only -->
# What the order-code is for: completeness and antisymmetry

The recursive order-code `_≤ᶜ_` of `QIITOrd.Order.Code` was hard-won — but so far it is
only *sound* (`encode≤ : α ≤ β → α ≤ᶜ β`) and otherwise unused. This module is the payoff:
it **consumes** the code to prove things about `_≤_` that are out of reach of direct
induction on the inductive order.

1. **Completeness** `decode≤ : α ≤ᶜ β → α ≤ β`, giving the exact characterisation
   `(α ≤ β) ≃ (α ≤ᶜ β)`.
2. **Irreflexivity** of `_<_`.
3. **Antisymmetry** `α ≤ β → β ≤ α → α ≡ β` — the flagship ordinal property, which the
   inductive `_≤_` cannot prove on its own (it has no successor- or limit-inversion
   constructor), but which falls out once the order is reflected into the computing code.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
module QIITOrd.Order.Antisymmetry where
open import QIITOrd.Base
open import QIITOrd.Properties
open import QIITOrd.Order.Code

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
```

## Completeness: `decode≤`

`decode≤` reconstructs an inductive `_≤_` derivation from a code, by double `elimProp` on
the two ordinals, reading off each computed clause of `_≤ᶜ_`. It is the converse of
`encode≤` and the paper's `Code→≤`. Note which induction hypothesis each case uses: the
*outer* one (on the first ordinal) for the `suc`/`suc` and `lim` cases, the *inner* one (on
the second) for the `suc`/`lim` case.

```agda
decode≤ : α ≤ᶜ β → α ≤ β
decode≤ {α} {β} = elimProp {P = λ α → (β : Ord) → α ≤ᶜ β → α ≤ β} Pprop Pz Ps Pl α β
  where
  Pprop : ∀ α → isProp ((β : Ord) → α ≤ᶜ β → α ≤ β)
  Pprop α = isPropΠ λ _ → isPropΠ λ _ → isProp≤

  Pz : (β : Ord) → zero ≤ᶜ β → zero ≤ β
  Pz β _ = z≤

  Ps : ∀ {α} → ((β : Ord) → α ≤ᶜ β → α ≤ β) → (β : Ord) → suc α ≤ᶜ β → suc α ≤ β
  Ps {α} IH = elimProp {P = λ β → suc α ≤ᶜ β → suc α ≤ β} Qprop Qz Qs Ql
    where
    Qprop : ∀ β → isProp (suc α ≤ᶜ β → suc α ≤ β)
    Qprop β = isPropΠ λ _ → isProp≤
    Qz : suc α ≤ᶜ zero → suc α ≤ zero
    Qz H = ⊥-rec H
    Qs : ∀ {β} → (suc α ≤ᶜ β → suc α ≤ β) → suc α ≤ᶜ suc β → suc α ≤ suc β
    Qs {β} _ H = s≤s (IH β H)
    Ql : ∀ {g} → (∀ n → (suc α ≤ᶜ fst g n → suc α ≤ fst g n)) → suc α ≤ᶜ lim g → suc α ≤ lim g
    Ql {g} ih H = rec isProp≤ (λ { (n , h) → ≤l (ih n h) }) H

  Pl : ∀ {f} → (∀ n → (β : Ord) → fst f n ≤ᶜ β → fst f n ≤ β) →
       (β : Ord) → lim f ≤ᶜ β → lim f ≤ β
  Pl {f} IH = elimProp {P = λ β → lim f ≤ᶜ β → lim f ≤ β} Rprop Rz Rs Rl
    where
    Rprop : ∀ β → isProp (lim f ≤ᶜ β → lim f ≤ β)
    Rprop β = isPropΠ λ _ → isProp≤
    Rz : lim f ≤ᶜ zero → lim f ≤ zero
    Rz H = ⊥-rec H
    Rs : ∀ {β} → (lim f ≤ᶜ β → lim f ≤ β) → lim f ≤ᶜ suc β → lim f ≤ suc β
    Rs {β} _ H = l≤ λ n → IH n (suc β) (H n)
    Rl : ∀ {g} → (∀ m → (lim f ≤ᶜ fst g m → lim f ≤ fst g m)) → lim f ≤ᶜ lim g → lim f ≤ lim g
    Rl {g} _ H = l≤ λ n → rec isProp≤ (λ { (m , h) → ≤-trans (IH n (fst g m) h) f≤l }) (H n)
```

## The characterisation `≤ ≃ ≤ᶜ`

Both `α ≤ β` and `α ≤ᶜ β` are propositions, so soundness and completeness package into an
**equivalence of types**: the inductive order *is* the recursive code.

```agda
≤≃≤ᶜ : (α ≤ β) ≃ (α ≤ᶜ β)
≤≃≤ᶜ = propBiimpl→Equiv isProp≤ isProp≤ᶜ encode≤ decode≤
```

With completeness in hand, we can lift cofinality of the code back to cofinality of the
order: `≼ᶜ→≼` maps `decode≤` under the existential truncation.

```agda
≼ᶜ→≼ : ∀ {s t} → s ≼ᶜ t → s ≼ t
≼ᶜ→≼ H n = rec squash₁ (λ { (m , h) → ∣ m , decode≤ h ∣₁ }) (H n)
```

## Irreflexivity of `_<_`

`α < α` is impossible. We show the code form `suc α ≤ᶜ α → ⊥` by `elimProp` on `α`: the
`zero` and `suc` cases are immediate, and the `lim f` case turns a witness
`suc (lim f) ≤ᶜ f[m]` into `f[m] < f[m]` (via `f≤l` and completeness) and applies the
induction hypothesis at `m`. Irreflexivity for `_<_` then follows by `encode≤`.

```agda
private
  noSuc≤ᶜ : suc α ≤ᶜ α → ⊥
  noSuc≤ᶜ {α} = elimProp {P = λ α → suc α ≤ᶜ α → ⊥} (λ _ → isProp→ isProp⊥) Qz Qs Ql α
    where
    Qz : suc zero ≤ᶜ zero → ⊥
    Qz H = ⊥-rec H
    Qs : ∀ {α} → (suc α ≤ᶜ α → ⊥) → suc (suc α) ≤ᶜ suc α → ⊥
    Qs IH H = IH H
    Ql : ∀ {f} → (∀ n → (suc (fst f n) ≤ᶜ fst f n → ⊥)) → suc (lim f) ≤ᶜ lim f → ⊥
    Ql {f} IH H = rec isProp⊥ (λ { (m , h) → IH m (encode≤ (≤-<-trans f≤l (decode≤ h))) }) H

<-irrefl : ¬ (α < α)
<-irrefl p = noSuc≤ᶜ (encode≤ p)
```

## Antisymmetry

The headline. We prove antisymmetry of the *code*, `≤ᶜ-antisym : α ≤ᶜ β → β ≤ᶜ α → α ≡ β`,
by nested `elimProp` on `α` and `β` (the motive `α ≡ β` is a proposition because `Ord` is a
set). The three diagonal cases are the content: `zero`/`zero` is `refl`; `suc`/`suc` is
`cong suc` of the induction hypothesis; and `lim`/`lim` turns the two code-cofinalities into
a genuine bisimulation (via `≼ᶜ→≼`) and applies the path constructor `l≡l`. Every *mixed*
case (`zero` vs non-`zero`, `suc` vs `lim`) is impossible and is discharged by reducing to a
strict self-inequality and invoking `<-irrefl`. Antisymmetry of `_≤_` then follows by
`encode≤` on both hypotheses.

```agda
≤ᶜ-antisym : α ≤ᶜ β → β ≤ᶜ α → α ≡ β
≤ᶜ-antisym {α} {β} =
  elimProp {P = λ α → (β : Ord) → α ≤ᶜ β → β ≤ᶜ α → α ≡ β} Pprop Pz Ps Pl α β
  where
  Pprop : ∀ α → isProp ((β : Ord) → α ≤ᶜ β → β ≤ᶜ α → α ≡ β)
  Pprop α = isPropΠ λ β → isPropΠ λ _ → isPropΠ λ _ → isSetOrd α β

  Pz : (β : Ord) → zero ≤ᶜ β → β ≤ᶜ zero → zero ≡ β
  Pz = elimProp {P = λ β → zero ≤ᶜ β → β ≤ᶜ zero → zero ≡ β}
    (λ β → isPropΠ λ _ → isPropΠ λ _ → isSetOrd zero β)
    (λ _ _ → refl)
    (λ _ _ H₂ → ⊥-rec H₂)
    (λ _ _ H₂ → ⊥-rec H₂)

  Ps : ∀ {α} → ((β : Ord) → α ≤ᶜ β → β ≤ᶜ α → α ≡ β) →
       (β : Ord) → suc α ≤ᶜ β → β ≤ᶜ suc α → suc α ≡ β
  Ps {α} IH = elimProp {P = λ β → suc α ≤ᶜ β → β ≤ᶜ suc α → suc α ≡ β}
    (λ β → isPropΠ λ _ → isPropΠ λ _ → isSetOrd (suc α) β)
    (λ H₁ _ → ⊥-rec H₁)
    (λ {β} _ H₁ H₂ → cong suc (IH β H₁ H₂))
    (λ _ H₁ H₂ → ⊥-rec (<-irrefl (≤-trans (decode≤ H₁) (l≤s⇒l≤ (decode≤ H₂)))))

  Pl : ∀ {f} → (∀ n → (β : Ord) → fst f n ≤ᶜ β → β ≤ᶜ fst f n → fst f n ≡ β) →
       (β : Ord) → lim f ≤ᶜ β → β ≤ᶜ lim f → lim f ≡ β
  Pl {f} IH = elimProp {P = λ β → lim f ≤ᶜ β → β ≤ᶜ lim f → lim f ≡ β}
    (λ β → isPropΠ λ _ → isPropΠ λ _ → isSetOrd (lim f) β)
    (λ H₁ _ → ⊥-rec H₁)
    (λ _ H₁ H₂ → ⊥-rec (<-irrefl (≤-trans (decode≤ H₂) (l≤s⇒l≤ (decode≤ H₁)))))
    (λ {g} _ H₁ H₂ → l≡l (≼ᶜ→≼ {fst f} {fst g} H₁ , ≼ᶜ→≼ {fst g} {fst f} H₂))

≤-antisym : α ≤ β → β ≤ α → α ≡ β
≤-antisym p q = ≤ᶜ-antisym (encode≤ p) (encode≤ q)
```
