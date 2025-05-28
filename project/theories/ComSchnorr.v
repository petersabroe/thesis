(* Imports and settings *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

From NominalSSP Require Import FsetSolve Group SSProve Nominal NomPackage Disjoint Prelude Sigma Schnorr Reductions.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.

From Project Require Import Com.


(* ----------------------------------------------------- *)
(* We create a module to implement the commitment scheme *)
(* ----------------------------------------------------- *)

Module ComSchnorr (GP: GroupParam).

(* Instantiate the Schnorr module of Nominal SSProve *)
Module S := Schnorr GP.

(* Instantiate the GroupTheorem module of Nominal SSProve *)
Module GT := GroupTheorems GP.

(* Import to bring all funtionality of above modules into current scope *)
Import GP GT S.

(* Proving that the types el and exp are inhabitated *)
#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.


(* Instantiating our raw_sigExt record with the raw_schnorr record 
   plus implementing sampl_challenge and key_gen *)
Definition raw_schnorrExt : raw_sigExt := 
  {| p := raw_schnorr

   ; sampl_challenge := 
     {code 
       e ← sample uniform #|exp| ;;
       ret e
     }

   ; key_gen :=
     {code 
       'w ← sample uniform #|exp| ;;
       ret (w, (fto (g ^+ otf w)))
     }
  |}.

(* Transforming raw_schnorrExt into a commitment scheme *) 
Definition raw_comSchnorr : raw_com := sig_to_com raw_schnorrExt.


(* THEOREMS *)

(* Proving correctness related to the correctness and SHVZK of the Schnorr sigma protocol *)
Theorem comSchnorr_Correct : Adv_Correct raw_comSchnorr (λ _, 0).
Proof.
  intros A.
  eapply le_trans.
  - apply Com_Correct_Correct.
  - rewrite -(add0r 0).
    apply lerD.
    + apply: (schnorr_SHVZK {adversary (Transcript raw_schnorr); (A ∘ Call_correct_sig raw_schnorrExt ∘ Verify_call raw_schnorrExt)}).
    + apply: (schnorr_Correct {adversary (ICorrect raw_schnorr); (A ∘ Call_correct_sig raw_schnorrExt)}).
Qed.


(* Proving perfect hiding - related to SHVZK of the Schnorr sigma protocol *)
Theorem comSchnorr_Hiding : Adv_Hiding raw_comSchnorr (λ _, 0).
Proof.
  intros A.
  eapply le_trans.
  - apply Com_hiding_SHVZK.
    + intros. apply NoFail_ret.
    + apply NoFail_sampler.
      * apply LosslessOp_uniform.
      * intros. apply NoFail_ret.
  - rewrite -(add0r 0).
    apply lerD.
    + apply: (schnorr_SHVZK {adversary (Transcript raw_schnorr); (A ∘ Call_SHVZK_inp raw_schnorrExt)}).
    + apply: (schnorr_SHVZK {adversary (Transcript raw_schnorr); (A ∘ Call_SHVZK_sam raw_schnorrExt)}).
Qed.


(* Proving computational binding - related to soundness of the Schnorr sigma protocol and hardness of the underlining relation *)
Theorem comSchnorr_Binding : Adv_Binding raw_comSchnorr (λ A, AdvFor (Hardness raw_schnorrExt) (A ∘ Call_Hardness raw_schnorrExt)).
Proof.
  intros A.
  eapply le_trans.
  - apply Com_Binding_Soundness_Rel.
  - rewrite -(add0r (AdvFor (λ b : bool, Hardness raw_schnorrExt b) (A ∘ Call_Hardness raw_schnorrExt))).
    apply lerD.
    + apply: (schnorr_Special_Soundness {adversary (Soundness raw_schnorr); (A ∘ Call_Soundness raw_schnorrExt)}).
    + rewrite GRing.add0r.
      apply le_refl.
Qed.
      


End ComSchnorr.








