# Verification_of_Axiom_free_Godelian_Ontological_Argument_and_Trinity_Necessity_Proof.thy

**Tested on Isabelle2025**

This repository accompanies the Isabelle/HOL theory
**`Verification_of_Axiom_free_Godelian_Ontological_Argument_and_Trinity_Necessity_Proof.thy`**.
It delivers a reusable, *axiom‑audited* framework for mechanizing **Gödel‑style ontological
arguments** and a **Trinitarian package** over a **definition‑only U‑layer**. The optional modal
material (S5‑like) is cleanly encapsulated in locales and **never leaks into the U‑core**.


# One‑Page Guide — Conclusions · Method · Significance
Verification_of_Axiom_free_Godelian_Ontological_Argument_and_Trinity_Necessity_Proof

**Purpose.** A compact, citable overview of the *entire codebase*: conclusions, method (how the proofs are structured), and significance. Ready to paste into your repo and the Isabelle document.

---

## Conclusions (what is proved)

- **Axiom‑free U‑core:** All order/epistemic/trinity machinery is *definition‑only* over `U`, `⊢`, `SuppU`, `≼`, `≈`, `TriSupport_le`, `EH/TH/PH` with `PH ⇔ (EH ∧ TH)`.
- **Consistency (within the core):** We **prove consistency of `H_opt`** and produce a **non‑trivial witness** `q ≠ ⊤` with `PH (Arg q)` — a truth‑based ontological result *without* modal axioms.
- **Cardinality ⇒ exactly three:** `n=1` excluded; `n=2` **impossibility** (collapse to `≈`); `n ≥ 4` impossible. Hence, whenever a configuration exists, there are **exactly three (up to `≈`)**.
  - **Sections 11.1 / 11.2:** The `n=2` *impossibility* is **assumption‑free**: it uses **no DN**, **no Tarski (E/I/C)**, and **all three locale assumptions (Core seed / Compat2 / PairCollapse_local) are discharged** in the Toy instance.
- **§12 D‑route (definitional, modal‑free):** Using **exactly three Tarski preservation clauses** — (E) `∃`, (I) `→`, (C) `∧` — we *derive reflection* and, from `Supports u (∃x. H x)`, obtain a **concrete witness** `a` with  
  `Supports u (H a ∧ A a ∧ B a ∧ C a)`. Combined with OnlyN3, this yields a **triune configuration at the actual point `u`**. No rigidity, no push, no S5.

---

## Method (how it is proved)

1. **U‑core (definition‑only):** introduce `U, ⊢`, define `SuppU`, `≼/≈/≺`, `Arg`, `Supports`, `◇ₑ`, `EH/TH/PH`, and **TriSupport_le**. Prove structural lemmas and `PH ⇔ (EH ∧ TH)`.
2. **Cardinality pipeline:** n=1 exclusion (witness against non‑EH), n=2 collapse/impossibility (EH‑pattern on EDia), n≥4 exclusion; conclude “exactly three” when existence holds.
3. **Bridges (safe):** `FullIdBridge` (definition‑only, extensional) and `ModalH_bridge` (conditional, no axioms added to U‑core).
4. **§12 D‑route locale:** assume **Tarski (E/I/C)** only; *derive* reflection from (E); lift pointwise TriSupport rules via (I)+(C); assemble the actual witness.
5. **Toy discharge (§11.2):** provide a concrete interpretation that **discharges all local assumptions** for the n=2 result, yielding a **premise‑free theorem** in HOL.

---

## Significance (why it matters)

- **Auditability & safety:** Optional assumptions are **scoped to locales**; the U‑core remains **axiom‑free**.
- **Assumption transparency:** Reflection is **derived** from Tarski (E); no rigid designators, no push, no S5.
- **Assumption‑free milestone:** The `n=2` impossibility stands **without DN or Tarski**; Toy discharges Core seed / Compat2 / PairCollapse_local.
- **Real reuse:** Others can adopt the U‑core alone, add their own bridges, or use the D‑route — without changing the kernel commitments.

---


## “How to refute” quick audit

- Deny **DN**: affects only a few `¬¬∃ → ∃` wrappers; structural results remain.
- Deny **Tarski (E/I/C)**: blocks §12; note this **abandons standard compositional (Tarskian) truth**, undermining mainstream model theory and much of mathematics in HOL.
- Deny **U‑definitions**: rejects conservative definitional extension in Isabelle/HOL and collapses the structural engine — not a meaningful refutation of this framework.

---

## Zero‑Axiom Promise (U‑core)

The U‑core fixes an abstract type `U` with primitive entailment `⊢`, then **defines**:

- support sets `SuppU`,
- the preorder `≼` and equivalence `≈` (via support‑set inclusion/equality),
- strict order `≺`,
- an epistemic bridge `Arg : bool ⇒ U`, pointwise support `Supports`, and the “epistemic possible`
  predicate `◇ₑ`,
- maximality schemas `EH`, `TH`, `PH` (with the internal equivalence `PH ⇔ (EH ∧ TH)`),
- trinitarian support pattern `TriSupport_le` and its *∀e* semantics (“pair ⇒ third” at every point).

> **Axiom status:** These are *pure definitions* and the U‑core lemmas are *definition‑theorems*
> only. No global axioms are introduced. “Axiom‑free” here means: **no user axioms** beyond
> HOL’s kernel and the declared constants/definitions in this theory.

---

## Where (and only where) assumptions appear

1. **Tarski Preservation, three clauses (Locale level, not global):**  
   In the *D‑route on U* we assume the standard Tarski clauses for model truth `Val`:
   - **(E)** Existential: `Val w (∃x. F x) ↔ (∃x. Val w (F x))`
   - **(I)** Implication: `Val w (P ⟶ Q) ↔ (Val w P ⟶ Val w Q)`
   - **(C)** Conjunction: `Val w (P ∧ Q) ↔ (Val w P ∧ Val w Q)`  
   These are used to lift U‑layer support to object‑level truth and to **derive** reflection.

2. **Double Negation (DN), used sparingly:**  
   DN is employed **only** to turn `¬¬∃` into `∃` in a few *extraction* lemmas (e.g., “DN→Hopt3”).
   All core order‑theoretic and trinitarian consequences **do not** rely on DN.

---

## Reflection is *derived* from Tarski ∃‑Preservation

From the clause `(E)` we obtain *witness reflection* at any world `w`. Specializing to the actual
world `u` delivers the “existence reflection” used by the D‑route: whenever an existential holds at
`u`, a concrete witness exists at `u`. No separate reflection axiom is assumed.

In short: **Reflection is not an assumption**; it is **provable from Tarski ∃‑preservation**.

---

## “What must be denied to refute the results?” — Assumption Audit

The core results separate into what is *definition‑driven* and what requires a minimal meta‑principle.
Use this matrix to see **exactly which lever** one must pull to block a given consequence.

| Principle (to deny) | Where it lives | What it blocks | Examples of impacted results |
|---|---|---|---|
| **U‑definitions** (`SuppU`, `≼/≈/≺`, `Arg`, `Supports`, `◇ₑ`, `EH/TH/PH`, `TriSupport_le`) | U‑core (definition‑only) | The entire order‑theoretic calculus and trinity semantics | `PH ⇔ (EH ∧ TH)`, `TriSupport_le` ⇒ ∀e (pair ⇒ third), n=2 collapse, n≥4 exclusion |
| **Tarski ∃‑preservation** (`Val w (∃x. F x) ↔ ∃x. Val w (F x)`) | Locale only (D‑route on U) | Any step that *extracts witnesses from existentials* at the model layer; hence the D‑route’s reflection steps | “Witness at `u`” lemmas; packaging that needs a concrete witness from `∃` |
| **Double Negation (DN)** (`¬¬∃ → ∃`) | Small number of extraction lemmas | Only the *DN‑based* conversions from possibility of existence to existence; **not** the structural order results | “DN→Hopt3”‑style results; convenience wrappers that turn `¬¬∃` into `∃` |

> **Important context.** Denying the **U‑definitions** amounts to rejecting Isabelle/HOL’s
> conservative‑definition discipline itself; that would undermine the kernel principles on which
> most formalized mathematics rests. Likewise, denying the **Tarski preservation clauses**
> (even just (E), (I), (C)) rejects standard *compositional semantics* for first‑order logic—
> breaking routine meta‑theorems (substitution, satisfaction of conjunction/implication, witness
> extraction for existentials). In practice, this amounts to disputing the semantic foundations
> used by the vast majority of modern mathematics and proof assistants.

> **Special case — n = 2 exclusion.** The n=2 impossibility is proved **without DN** and **without
> any Tarski clauses**; moreover, in §11.2 all local/locale assumptions are **discharged**, yielding
> a 100% **assumption‑free, axiom‑free** theorem inside HOL.

---

## Highlights

- **Axiom‑free U‑core.** All order/epistemic/trinity machinery is defined and proved with no user axioms.
- **Two reusable bridges (U‑safe).**
  - **`FullIdBridge` (definition‑only):** links model truth `Val` and U‑support via an embedding `iw`.
  - **`ModalH_bridge` (conditional):** if `H X ⟹ PH (Arg X)` holds externally, you inherit the trinitarian package—without touching the U‑layer.
- **Trinity package with non‑collapse guard.** `TriSupport_le` yields the universal *(pair ⇒ third)* semantics; the (T)+(S) pattern avoids collapsing `Trinity ⇒ R` when `R` is contingent.
- **Cardinality theorems (U‑core).** n=1 exclusion (witness style), n=2 collapse to `≈`, and n≥4 impossibility. Hence, where a configuration exists, it is **exactly three (up to `≈`)**.
- **Riemann Toy Model (executable).** Shows why a PH‑candidate must be supported by all epistemic possibilities (`◇ₑ`), not only current truths.

---

## Section 11.1 / 11.2 — n = 2 Impossibility is Assumption‑Free (Epistemic‑Only Path)

**Section 11.1 (`n = 2` impossibility, epistemic‑only).**  
Assuming there are *exactly two* semantically distinct `H`‑arguments `φ, ω` leads to a contradiction:
`PH ⇒ EH`, and with both `EDia` (epistemically possible), the **EH‑pattern** yields mutual inclusion of their
`Arg`‑supports, hence `Arg φ ≈ Arg ω`. Therefore there cannot exist “exactly two non‑EqU‑equivalent H‑arguments.”
This uses **no Tarski clauses and no DN**—only U‑core machinery.

**Section 11.2 (Toy, discharging all locale assumptions).**  
A toy interpretation **discharges all three local assumptions** used for the `n = 2` exclusion:
(1) *Core seed* (`H_not_refuted`), (2) *Compat2* (live‑option compatibility), and (3) *PairCollapse_local*.
All types are instantiated with `unit` and `Arg` is constant; obligations are solved by `simp`. The resulting corollary

```
Toy_n2_exclusion_global:
  ¬ (∃a b. Hopt_toy a ∧ Hopt_toy b ∧ Arg_toy (H_toy a) ≠ Arg_toy (H_toy b))
```

is **premise‑free and axiom‑free** inside HOL.  
**Bottom line:** the `n = 2` impossibility is obtained *without* DN and *without* any of the three Tarski clauses—
and with all locale assumptions explicitly **discharged**.

---

## How this differs from prior Gödel mechanizations

- Prior work often bakes in **strong modal/essentiality axioms** early; here the **U‑core is
  definition‑only**, and any modal strength is **confined to locales**.
- **Existence reflection** is *not postulated*: it **follows from** Tarski (E).
- Many key consequences (PH structure, trinity semantics, cardinality facts) are **purely
  order‑theoretic** and **modal‑free**.
- The **bridge architecture** lets others reuse just the pieces they want (U‑core only, model
  embedding, or a conditional Gödel track), improving AFP safety and assumption transparency.

---

## Files

- `theory/Verification_of_Axiom_free_Godelian_Ontological_Argument_and_Trinity_Necessity_Proof.thy`  
  The complete framework (U‑layer core, trinity tools, maximality families, cardinality theorems,
  optional modal locales, bridges, and the `Riemann_Toy` instance).

If your local filename differs, please keep the README title in sync with your canonical theory name.

---

## Building

1. Install Isabelle/HOL (Isabelle2025 recommended; 2022+ generally works).
2. Place the `.thy` file under your session’s `theory/` directory and add it to your `ROOT` if needed.
3. Build with the IDE (Isabelle/jEdit) or CLI:  
   ```bash
   isabelle build -D . -v
   ```

No AFP dependencies are required for the U‑core. Optional modal locales are self‑contained.

---

## Reuse Patterns (with a worked example)

### 1) Conditional Gödel track (`ModalH_bridge`)
Provide an external predicate `H : bool ⇒ bool` and a single lemma inside the bridge locale:
```isabelle
assumes H_to_PH: "⋀X. H X ⟹ PH (Arg X)"
```
Then, for any `Φ, Ω, Ψ` with `H Φ`, `H Ω`, `H Ψ` and each `EDia`, you get:
- `TriSupport_le (Arg Φ) (Arg Ω) (Arg Ψ)`,
- all pairwise `≈` among `Arg Φ, Arg Ω, Arg Ψ`,
- the ∀e *(pair ⇒ third)* semantics.

### 2) Model‑theoretic embedding (`FullIdBridge`, definition‑only)
Instantiate `Val : 'W ⇒ bool ⇒ bool` and `iw : 'W ⇒ U` so that
```isabelle
(iw w ⊢ Arg ζ) ↔ Val w ζ
```
Model‑level subset facts immediately yield U‑order facts (`⊆` ⇒ `≼`). This is **definition‑only**
and safe for U‑core reuse.

### Worked example: `Riemann_Toy`
Two worlds `I, II` with `Val I R` and `¬ Val II R`. Inside the locale we show `EDia R` and that
`(Arg R) ≼ (Arg Φ)` but not `(Arg R) ≼ (Arg Φ')`, hence `¬ PH (Arg Φ')`. The example demonstrates
that **PH requires support from all epistemic possibilities**, not only current truths.

---

## What is *not* assumed

- No global axioms on `U`, no comprehension beyond HOL’s kernel.
- No modal axioms outside optional locales.
- No hidden rigidity, essentialism, or “push”‑style assumptions.
- DN is *not* required for the structural/calculus parts; it appears only in a few “`¬¬∃ → ∃`” wrappers.

---

## Minimal Trinitarian Pattern (ready‑to‑paste)

```isabelle
(* Three‑way support relation, lifted to ∀e semantics *)
TriSupport_le (Arg a) (Arg b) (Arg c)

(* Derived pointwise rules: *)
∀e. (Supports e b ∧ Supports e c) ⟶ Supports e a
∀e. (Supports e c ∧ Supports e a) ⟶ Supports e b
∀e. (Supports e a ∧ Supports e b) ⟶ Supports e c
```

Pairwise `≈` among `(Arg a, Arg b, Arg c)` is available from the core lemmas when each of `a, b, c`
meets the relevant maximality/possibility side‑conditions spelled out in the theory file.

---

## License & Citation

- **License:** MIT (suggested; adapt as needed).
- **Citation:** “Mechanized Verification of Gödel‑style Ontological Arguments and Trinitarian
  Metaphysics in Isabelle/HOL,” with a link to a stable snapshot or commit of your fork.

---

## Maintainers & Contributions

Contributions are welcome: additional external `H` bridges, alternative model embeddings,
and refinements of the cardinality/uniqueness landscape that reuse the U‑core.

---

## Proof Provenance (one‑page map)

**[U] = U‑layer (axiom‑free)** · **[Loc] = Locales (assumptions scoped)**

- **[U]** `SuppU`, `≼/≈/≺`, `Arg`, `Supports`, `◇ₑ`, `EH/TH/PH`, `PH ⇔ (EH ∧ TH)`.
- **[U]** `TriSupport_le` and its ∀e semantics; n=1 exclusion; n=2 collapse; n≥4 impossibility.
- **[Loc]** Tarski (E/I/C) ⇒ reflection (no global reflection axiom).
- **[Loc]** Optional S5‑style locales; their axioms remain sealed and never bleed into [U].
- **[U/Loc]** Bridges (`FullIdBridge`, `ModalH_bridge`) provide reuse paths without strengthening [U].

**n = 2 status (Sections 11.1 / 11.2):** *assumption‑free result*. No DN, no Tarski, and all three
local assumptions are discharged in the Toy instance, yielding a premise‑free theorem inside HOL.

## Optional Diagnostics

To reproduce the **axiom-assumption-free audit**:
1. Build the session `Axiom_And_Assumption_Audit.thy`.
2. This generates `document/axiom_and_assumption_audit.txt`.
3. The PDF will automatically embed the audit log.

It confirms that the entire development uses **no axioms**
(other than the Tarski-preservation lemmas and DN, which are
explicitly listed).