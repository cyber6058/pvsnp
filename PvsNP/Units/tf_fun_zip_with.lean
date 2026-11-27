import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner (`pairB`, `unpairB`, `Iter.iter_polyTime`),
m2_ite_polytime, m2_dfa_in_p, and m2_polytime_comp of github.com/makedotfun/pvsnp
(Apache License 2.0).
-/

/-
SPDX-License-Identifier: Apache-2.0
Adapted from PvsNP/Units/m2_zip_bne_polytime.lean, github.com/makedotfun/pvsnp,
at commit 81a25475d739668f925eea59e7bef587de6cb214 under the Apache License, Version 2.0.
Modifications: use conjunction for each pair of input bits, simplify the step machine,
and specialize the iterator's correctness proof to conjunction.
-/

namespace PvsNP.Units.tf_fun_zip_with_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem unpairB_len_bound (s : List Bool) :
    (unpairB s).1.length + (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

private theorem pairB_length (a b : List Bool) :
    (pairB a b).length = a.length + a.length + b.length + 1 := by
  simp only [pairB, List.length_append, un_length, List.length_cons]
  omega

private theorem nonempty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => !x.isEmpty) := by
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p Bool (fun _ _ => true) false id
  have hfold_true : ∀ y : List Bool, y.foldl (fun _ _ => true) true = true := by
    intro y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => !x.isEmpty := by
    funext x
    have hx := hdec x
    change id (x.foldl (fun _ _ => true) false) = true ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, id, List.isEmpty_nil, Bool.not_true] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, hfold_true, id, List.isEmpty_cons, Bool.not_false] at hx ⊢
      exact hx.1 trivial
  rwa [← heq]

private theorem headD_false_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => x.headD false := by
    funext x
    have hx := hdec x
    change ((x.foldl δ none == some true) = true) ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, List.headD_nil] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, δ, hfold_some, List.headD_cons] at hx ⊢
      cases b with
      | false => cases hcx : c (false :: y) <;> simp_all
      | true => exact hx.1 (by decide)
  rwa [← heq]

private def sA (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
private def sB (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
private def sAcc (s : List Bool) : List Bool := (unpairB s).2

private def zStep (s : List Bool) : List Bool :=
  if !(sA s).isEmpty = true then
    if !(sB s).isEmpty = true then
      if (sA s).headD false = true then
        if (sB s).headD false = true then
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [true])
        else
          pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [false])
      else
        pairB (pairB (sA s).tail (sB s).tail) (sAcc s ++ [false])
    else
      pairB (pairB (sA s) (sB s)) (sAcc s)
  else
    pairB (pairB (sA s) (sB s)) (sAcc s)

private theorem zStep_len (s : List Bool) : (zStep s).length ≤ s.length + 5 := by
  have h1 := unpairB_len_bound s
  have h2 := unpairB_len_bound (unpairB s).1
  have ha : (sA s).tail.length ≤ (sA s).length := by simp
  have hb : (sB s).tail.length ≤ (sB s).length := by simp
  have hbound : 4 * (sA s).length + 2 * (sB s).length + (sAcc s).length ≤ s.length := by
    unfold sA sB sAcc; omega
  unfold zStep
  split_ifs <;> simp only [pairB_length, List.length_append, List.length_singleton] <;> omega

private theorem zStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString zStep := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sA :=
    cpt_unpairB1_1 cpt_unpairB1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sB :=
    cpt_unpairB2_1 cpt_unpairB1
  have hAcc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sAcc :=
    cpt_unpairB2
  have hAne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sA (fun x => !x.isEmpty) hA nonempty_poly
  have hBne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sB (fun x => !x.isEmpty) hB nonempty_poly
  have hAhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sA (fun x => x.headD false) hA headD_false_poly
  have hBhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    sB (fun x => x.headD false) hB headD_false_poly
  have hpairT := cpt_pairB2 (cpt_tail1 hA) (cpt_tail1 hB)
  have hpush0 := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [false]))
  have hpush1 := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [true]))
  have hstay := cpt_pairB2 (cpt_pairB2 hA hB) hAcc
  have h1 := PvsNP.Units.m2_ite_polytime _ _ _ hBhd hpush1 hpush0
  have h3 := PvsNP.Units.m2_ite_polytime _ _ _ hAhd h1 hpush0
  have h4 := PvsNP.Units.m2_ite_polytime _ _ _ hBne h3 hstay
  exact PvsNP.Units.m2_ite_polytime _ _ _ hAne h4 hstay

private theorem zStep_stay_nil_right (m : ℕ) (a acc : List Bool) :
    (unpairB (zStep^[m] (pairB (pairB a []) acc))).2 = acc := by
  induction m generalizing a acc with
  | zero => simp [unpairB_pairB]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hs : zStep (pairB (pairB a []) acc) = pairB (pairB a []) acc := by
      unfold zStep sA sB sAcc
      cases a <;> simp [unpairB_pairB]
    rw [hs]
    exact ih a acc

private theorem zStep_iter (a b acc : List Bool) :
    (unpairB (zStep^[a.length] (pairB (pairB a b) acc))).2 =
      acc ++ List.zipWith (fun x y : Bool => x && y) a b := by
  induction a generalizing b acc with
  | nil =>
    simp [unpairB_pairB]
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [List.zipWith_nil_right, List.append_nil]
      exact zStep_stay_nil_right (x :: a).length (x :: a) acc
    | cons y b =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hs : zStep (pairB (pairB (x :: a) (y :: b)) acc) =
          pairB (pairB a b) (acc ++ [x && y]) := by
        unfold zStep sA sB sAcc
        simp only [unpairB_pairB, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
          List.headD_cons, List.tail_cons]
        cases x <;> cases y <;> rfl
      rw [hs, ih b (acc ++ [x && y])]
      simp [List.append_assoc]

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a && b) p.1 p.2) := by
  obtain ⟨cz⟩ := zStep_poly
  have hiter : PvsNP.PolyTimeComputable PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.encodeString (fun p : List Bool × List Bool => zStep^[p.2.length] p.1) :=
    Iter.iter_polyTime zStep cz 5 zStep_len
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    rw [← encodePair_eq]
    exact cpt_pairB
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => pairB s []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hrunS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB (zStep^[(unpairB s).1.length] (pairB s []))).2) :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit cpt_unpairB1) hiter)
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => pairB p.1 p.2)
    (fun s : List Bool => (unpairB (zStep^[(unpairB s).1.length] (pairB s []))).2) hpb hrunS
  have heq :
      ((fun s : List Bool => (unpairB (zStep^[(unpairB s).1.length] (pairB s []))).2) ∘
        (fun p : List Bool × List Bool => pairB p.1 p.2)) =
      (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a && b) p.1 p.2) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB]
    have h := zStep_iter a b []
    simpa using h
  rwa [heq] at hcomp

end PvsNP.Units.tf_fun_zip_with_aux

theorem PvsNP.Units.tf_fun_zip_with :
PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) := by
  exact PvsNP.Units.tf_fun_zip_with_aux.main
