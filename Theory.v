Require Import Omega.
Require Import Bool.
Require Import FunctionalExtensionality.

(* Abstract Variable Type *)
Module Type VARIABLE.
  Parameter var        : Type.
  Parameter var_eq_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
End VARIABLE.

(* Semantic Value Type *)
Module Type SEM_VAL.
  Parameter Val : Set.
  Parameter val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
  Parameter truth_and : Val -> Val -> Val.
  Parameter truth_or : Val -> Val -> Val.
  Parameter truth_not : Val -> Val.
  Parameter Top : Val.
  Parameter Btm : Val.
  Axiom bool_inj_not_eq : Top <> Btm.
  Axiom truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Axiom truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Axiom truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Axiom truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Axiom truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top <-> v1 = Top \/ v2 = Top.
  Axiom truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top <-> v1 = Top /\ v2 = Top.
  Axiom truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm <-> v1 = Btm /\ v2 = Btm.
  Axiom truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm <-> v1 = Btm \/ v2 = Btm.
  Axiom tautology_1 : truth_not Btm = Top.
  Axiom tautology_2 : truth_not Top = Btm.
  Axiom tautology_3 : forall v, truth_and v v = v.
  Axiom tautology_4 : truth_and Top Btm = Btm.
  Axiom tautology_5 : truth_and Btm Top = Btm.
  Axiom tautology_6 : forall v, truth_or v v = v.
  Axiom tautology_7 : truth_or Top Btm = Top.
  Axiom tautology_8 : truth_or Btm Top = Top.

End SEM_VAL.

Module Three_Val <: SEM_VAL.

  Inductive Val_Impl := VTrue | VFalse | VUnknown.
  Definition Val := Val_Impl.

  Definition val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
    intros; destruct v1, v2; intuition; right; intro; inversion H.
  Defined.

  Definition Top := VTrue.
  Definition Btm := VFalse.

  Lemma bool_inj_not_eq: Top <> Btm.
  Proof. intro; inversion H. Qed.

  Definition truth_and (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue    , VTrue    => VTrue
      | VTrue    , VUnknown => VUnknown
      | VTrue    , VFalse   => VFalse
      | VUnknown , VTrue    => VUnknown
      | VUnknown , VUnknown => VUnknown
      | VUnknown , VFalse   => VFalse
      | VFalse   , _        => VFalse
    end.

  Definition truth_or (v1 v2 : Val) :=
    match v1, v2 with
      | VTrue    , _        => VTrue
      | VUnknown , VTrue    => VTrue
      | VUnknown , VUnknown => VUnknown
      | VUnknown , VFalse   => VUnknown
      | VFalse   , VTrue    => VTrue
      | VFalse   , VUnknown => VUnknown
      | VFalse   , VFalse   => VFalse
    end.

  Definition truth_not v :=
    match v with
      | VTrue    => VFalse
      | VUnknown => VUnknown
      | VFalse   => VTrue
    end.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top <-> v1 = Top \/ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top <-> v1 = Top /\ v2 = Top.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm <-> v1 = Btm /\ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

  Lemma truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm <-> v1 = Btm \/ v2 = Btm.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma tautology_1 : truth_not Btm = Top. Proof. intuition. Qed.
  Lemma tautology_2 : truth_not Top = Btm. Proof. intuition. Qed.
  Lemma tautology_3 : forall v, truth_and v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_4 : truth_and Top Btm = Btm. Proof. intuition. Qed.
  Lemma tautology_5 : truth_and Btm Top = Btm. Proof. intuition. Qed.
  Lemma tautology_6 : forall v, truth_or v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_7 : truth_or Top Btm = Top. Proof. intuition. Qed.
  Lemma tautology_8 : truth_or Btm Top = Top. Proof. intuition. Qed.

End Three_Val.

Module Bool_Val <: SEM_VAL.
  Definition Val := bool.
  Definition truth_and := andb.
  Definition truth_or := orb.
  Definition truth_not := negb.
  Definition Top := true.
  Definition Btm := false.
  Definition val_eq_dec : forall v1 v2 : Val, {v1 = v2} + {v1 <> v2}.
    intros; destruct v1, v2; intuition; right; intro; inversion H.
  Defined.

  Lemma bool_inj_not_eq: Top <> Btm. Proof. intro; inversion H. Qed.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = Top <-> v1 = Top \/ v2 = Top.
  Proof. intros; simpl; apply orb_true_iff. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = Top <-> v1 = Top /\ v2 = Top.
  Proof. intros; simpl; apply andb_true_iff. Qed.

  Lemma truth_or_false_iff : forall v1 v2, truth_or v1 v2 = Btm <-> v1 = Btm /\ v2 = Btm.
  Proof. intros; simpl; apply orb_false_iff. Qed.

  Lemma truth_and_false_iff : forall v1 v2, truth_and v1 v2 = Btm <-> v1 = Btm \/ v2 = Btm.
  Proof. intros; simpl; apply andb_false_iff. Qed.

  Lemma tautology_1 : truth_not Btm = Top. Proof. intuition. Qed.
  Lemma tautology_2 : truth_not Top = Btm. Proof. intuition. Qed.
  Lemma tautology_3 : forall v, truth_and v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_4 : truth_and Top Btm = Btm. Proof. intuition. Qed.
  Lemma tautology_5 : truth_and Btm Top = Btm. Proof. intuition. Qed.
  Lemma tautology_6 : forall v, truth_or v v = v. Proof. intros; destruct v; simpl; trivial. Qed.
  Lemma tautology_7 : truth_or Top Btm = Top. Proof. intuition. Qed.
  Lemma tautology_8 : truth_or Btm Top = Top. Proof. intuition. Qed.

End Bool_Val.

Module Type NUMBER.
  Parameter A          : Type.
  Parameter Const0     : A.
  Parameter num_eq_dec : forall n1 n2 : A, {n1 = n2} + {n1 <> n2}.
  Parameter num_neg    : A -> A.
  Parameter num_plus   : A -> A -> A.
End NUMBER.

(* Pure Integer including Infinity *)
Module ZInfinity <: NUMBER.

  Inductive ZE : Type :=
  | ZE_Fin     : Z -> ZE
  | ZE_Inf     : ZE
  | ZE_NegInf  : ZE.

  Definition ZE_eq_dec : forall ze1 ze2 : ZE, {ze1 = ze2} + {ze1 <> ze2}.
  Proof.
    destruct ze1; destruct ze2; auto; try (right; intro; discriminate).
    destruct (Z_eq_dec z z0). left; congruence.
    right; congruence.
  Defined.

  (* Negation with Infinity *)
  Definition ZEneg (ze : ZE) : ZE :=
    match ze with
        ZE_Fin z  => ZE_Fin (- z)
      | ZE_Inf    => ZE_NegInf
      | ZE_NegInf => ZE_Inf
    end.

  Definition A := option ZE.
  Definition Const0 := Some (ZE_Fin 0).

  Definition num_eq_dec : forall n1 n2 : A, {n1 = n2} + {n1 <> n2}.
  Proof.
    intros. destruct n1, n2; auto.
    destruct (ZE_eq_dec z z0).
    left; f_equal; auto.
    right; congruence.
    right; congruence.
    right; congruence.
  Defined.

  Definition num_neg := option_map ZEneg.

  (* Addition with Infinity *)
  Definition num_plus (ze1 ze2 : option ZE) : option ZE :=
    match ze1, ze2 with
      | None, _
      | _, None
      | Some ZE_Inf, Some ZE_NegInf
      | Some ZE_NegInf, Some ZE_Inf        => None
      | Some ZE_Inf, _
      | _, Some ZE_Inf                     => Some ZE_Inf
      | Some ZE_NegInf, _
      | _, Some ZE_NegInf                  => Some ZE_NegInf
      | Some (ZE_Fin z1), Some (ZE_Fin z2) => Some (ZE_Fin (z1 + z2))
    end.

  (* If sum is finite, then both addend and augend are finite. *)
  Lemma numplus_finite : forall v1 v2 z, num_plus v1 v2 = Some (ZE_Fin z)
                                         -> exists z1 z2, (v1 = Some (ZE_Fin z1)) /\
                                                          (v2 = Some (ZE_Fin z2)) /\
                                                          (z1 + z2 = z)%Z.
  Proof.
    intros until z.
    destruct v1, v2; intros; try discriminate H.
    destruct z0, z1; try discriminate H.
    exists z0, z1; simpl in *.
    split; auto.
    split; auto.
    injection H; auto.
    destruct z0; discriminate H.
  Qed.

  (* If negation is finite, then the original is finite. *)
  Lemma numneg_finite : forall v z, num_neg v = Some (ZE_Fin z)
                                    -> exists x, v = Some (ZE_Fin x) /\ (- x = z)%Z.
  Proof.
    intros until z.
    destruct v; intros; try discriminate H.
    destruct z0; try discriminate H.
    exists z0.
    split; auto.
    simpl in H.
    injection H.
    auto.
  Qed.

  (* If sum is positive infinity, then at least one addend is positive
  infinity and neither of them is negative infinity. *)
  Lemma numplus_inf : forall v1 v2, num_plus v1 v2 = Some ZE_Inf
                                    -> ((exists z, v1 = Some (ZE_Fin z)) /\ v2 = Some ZE_Inf) \/
                                       (v1 = Some ZE_Inf /\ (exists z, v2 = Some (ZE_Fin z))) \/
                                       (v1 = Some ZE_Inf /\ v2 = Some ZE_Inf).
  Proof.
    intros.
    destruct v1, v2.
    destruct z, z0; simpl in *; auto;
    try (discriminate H).
    left; split; auto; exists z; auto.
    right; left; split; auto; exists z; auto.
    simpl in H; destruct z; discriminate H.
    simpl in H; destruct z; discriminate H.
    simpl in H; discriminate H.
  Qed.

  (* If sum is negative infinity, then at least one addend is negative
  infinity and neither of them is positive infinity. *)
  Lemma numplus_neginf : forall v1 v2, num_plus v1 v2 = Some ZE_NegInf
                                       -> ((exists z, v1 = Some (ZE_Fin z)) /\ v2 = Some ZE_NegInf) \/
                                          (v1 = Some ZE_NegInf /\ (exists z, v2 = Some (ZE_Fin z))) \/
                                          (v1 = Some ZE_NegInf /\ v2 = Some ZE_NegInf).
  Proof.
    intros.
    destruct v1, v2.
    destruct z, z0; simpl in *; auto;
    try (discriminate H).
    left; split; auto; exists z; auto.
    right; left; split; auto; exists z; auto.
    simpl in H; destruct z; discriminate H.
    simpl in H; destruct z; discriminate H.
    simpl in H; discriminate H.
  Qed.

  (* If negation is positive infinity, then the original is negative infinity. *)
  Lemma numneg_inf : forall v, num_neg v = Some ZE_Inf
                               -> v = Some (ZE_NegInf).
  Proof.
    destruct v; intros; try discriminate H.
    destruct z; try discriminate H.
    auto.
  Qed.

  (* If negation is negative infinity, then the original is positive infinity. *)
  Lemma numneg_neginf : forall v, num_neg v = Some ZE_NegInf
                                  -> v = Some (ZE_Inf).
  Proof.
    destruct v; intros; try discriminate H.
    destruct z; try discriminate H.
    auto.
  Qed.

  (* If sum has no definition, then either of addends has no
  definition or it's the sum of positive infinity and negative
  infinity. *)
  Lemma numplus_none : forall v1 v2, num_plus v1 v2 = None -> v1 = None \/ v2 = None \/
                                                              (v1 = Some ZE_Inf /\ v2 = Some ZE_NegInf) \/
                                                              (v1 = Some ZE_NegInf /\ v2 = Some ZE_Inf).
  Proof.
    intros.
    destruct v1, v2.
    right; right.
    destruct z, z0; try discriminate H.
    left; auto.
    right; auto.
    right; left; auto.
    left; auto.
    left; auto.
  Qed.

  (* If the negation has no definition, then the original has no definition *)
  Lemma numneg_none: forall v, num_neg v = None -> v = None.
  Proof.
    intros.
    destruct v.
    destruct z; simpl in H; discriminate H.
    auto.
  Qed.

End ZInfinity.

(* Normal Integer Number Field *)
Module ZNumLattice <: NUMBER.
  Definition A := Z.
  Definition Const0 := 0%Z.
  Definition num_eq_dec := Z_eq_dec.
  Definition num_neg (x : A) := (0 - x)%Z.
  Definition num_plus (x y : A) := (x + y)%Z.
End ZNumLattice.

Module Type LEQ_RELATION (NUM : NUMBER) (VAL : SEM_VAL).
  Import NUM.
  Import VAL.
  Parameter num_leq : A -> A -> Val.
End LEQ_RELATION.

Module FinLeqRelation (VAL : SEM_VAL) <: LEQ_RELATION ZNumLattice VAL.
  Import ZNumLattice.
  Import VAL.
  Definition num_leq (x y : A) := if Z_le_dec x y then Top else Btm.
End FinLeqRelation.

Module Type NONE_RELATION (VAL : SEM_VAL).
  Import VAL.
  Parameter noneVal : Val.
  Axiom none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal.
  Axiom none_tautology_2 : truth_and noneVal Top = noneVal.
  Axiom none_tautology_3 : truth_and noneVal Btm = Btm.
  Axiom none_tautology_4 : truth_or noneVal Btm = noneVal.
  Axiom none_tautology_5 : truth_or Btm noneVal = noneVal.
End NONE_RELATION.

Module None3ValRel <: NONE_RELATION Three_Val.
  Import Three_Val.
  Definition noneVal := VUnknown.
  Lemma none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_2 : truth_and noneVal Top = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_3 : truth_and noneVal Btm = Btm. Proof. intuition. Qed.
  Lemma none_tautology_4 : truth_or noneVal Btm = noneVal. Proof. intuition. Qed.
  Lemma none_tautology_5 : truth_or Btm noneVal = noneVal. Proof. intuition. Qed.

End None3ValRel.

Module NoneAlwaysFalse (VAL : SEM_VAL) <: NONE_RELATION VAL.
  Import VAL.
  Definition noneVal := Btm.
  Lemma none_tautology_1 : truth_and noneVal (truth_not noneVal) = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_1, tautology_5; trivial. Qed.

  Lemma none_tautology_2 : truth_and noneVal Top = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_5; trivial. Qed.

  Lemma none_tautology_3 : truth_and noneVal Btm = Btm.
  Proof. unfold noneVal; simpl; rewrite tautology_3; trivial. Qed.

  Lemma none_tautology_4 : truth_or noneVal Btm = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_6; trivial. Qed.

  Lemma none_tautology_5 : truth_or Btm noneVal = noneVal.
  Proof. unfold noneVal; simpl; rewrite tautology_6; trivial. Qed.

End NoneAlwaysFalse.

Module InfLeqRelation (VAL : SEM_VAL) (S: NONE_RELATION VAL) <: LEQ_RELATION ZInfinity VAL.
  Import ZInfinity.
  Import VAL.
  Import S.
  (* Definition of relation "less than or equal to" *)
  Definition num_leq (ze1 ze2 : A) : Val :=
    match ze1, ze2 with
      | None, _
      | _, None                            => noneVal
      | _, Some ZE_Inf                     => Top
      | Some ZE_NegInf, _                  => Top
      | Some ZE_Inf, Some x                => if ZE_eq_dec x ZE_Inf then Top else Btm
      | Some x, Some ZE_NegInf             => if ZE_eq_dec x ZE_NegInf then Top else Btm
      | Some (ZE_Fin z1), Some (ZE_Fin z2) => if Z_le_dec z1 z2 then Top else Btm
    end.
End InfLeqRelation.

(* Intermediate Modules *)
(* Abstract type which separates variable domain and constant domain *)
Module Type SEMANTICS_INPUT.
  Declare Module N : NUMBER.
  Import N.
  Parameter Q      : Type.
  Parameter QT     : Q -> Type.
  Parameter conv   : forall q, (QT q) -> A.
End SEMANTICS_INPUT.

(* Variable domain can be integer with infinity or just
integer. Constant domain is integer with infinity. *)
Module PureInfinity <: SEMANTICS_INPUT.
  Module N := ZInfinity.
  Import N.
  Inductive AQ : Type :=
    Q_Z | Q_ZE.
  Definition Q : Type := AQ.
  Definition QT (q : Q) : Type := match q with Q_Z => Z | Q_ZE => ZE end.
  Definition conv {q : Q} (x : QT q) : A :=
    match q return (QT q -> A) with
      | Q_Z => fun x : Z => Some (ZE_Fin x)
      | Q_ZE => fun x : ZE => Some x
    end x.
End PureInfinity.

(* Both domains are integer. *)
Module PureInt <: SEMANTICS_INPUT.
  Module N := ZNumLattice.
  Definition Q := unit.
  Definition QT (q : Q) : Type := Z.
  Definition conv {q : Q} (x : QT q) := x.
End PureInt.

(* Variable domain is integer and constant domain is integer with infinity. *)
Module IntToInfinity <: SEMANTICS_INPUT.
  Module N := ZInfinity.
  Import N.
  Definition Q := unit.
  Definition QT (q : Q) : Type := Z.
  Definition conv {q : Q} (x : QT q) := Some (ZE_Fin x).
End IntToInfinity.

Module ArithSemantics (I : SEMANTICS_INPUT) (V : VARIABLE) (VAL : SEM_VAL) (S: NONE_RELATION VAL) (L : LEQ_RELATION I.N VAL).
  Import I N V VAL S L.

  (* Syntax *)
  Section OriginalForm.

    (* Arithmetic Expression *)
    Inductive ZExp : Type :=
    | ZExp_Var     : var  -> ZExp
    | ZExp_Const   : A    -> ZExp
    | ZExp_Add     : ZExp -> ZExp -> ZExp (* + *)
    | ZExp_Inv     : ZExp -> ZExp (* unary - *)
    | ZExp_Sub     : ZExp -> ZExp -> ZExp (* - *)
    | ZExp_Mult    : Z    -> ZExp -> ZExp. (* Constant Multiplication *)

    (* Boolean Forms *)
    Inductive ZBF : Type :=
    | ZBF_Const   : Val -> ZBF
    | ZBF_Lt      : ZExp -> ZExp -> ZBF (* < *)
    | ZBF_Lte     : ZExp -> ZExp -> ZBF (* <= *)
    | ZBF_Gt      : ZExp -> ZExp -> ZBF (* > *)
    | ZBF_Gte     : ZExp -> ZExp -> ZBF (* >= *)
    | ZBF_Eq      : ZExp -> ZExp -> ZBF (* = *)
    | ZBF_Eq_Max  : ZExp -> ZExp -> ZExp -> ZBF (* a = min(b, c) *)
    | ZBF_Eq_Min  : ZExp -> ZExp -> ZExp -> ZBF (* a = max(b, c) *)
    | ZBF_Neq     : ZExp -> ZExp -> ZBF. (* <> *)

    (* Logic Forms *)
    Inductive ZF : Type :=
    | ZF_BF      : ZBF -> ZF
    | ZF_And     : ZF  -> ZF -> ZF (* /\ *)
    | ZF_Or      : ZF  -> ZF -> ZF (* \/ *)
    | ZF_Imp     : ZF  -> ZF -> ZF (* -> *)
    | ZF_Not     : ZF  -> ZF       (* ~ *)
    | ZF_Forall  : var -> Q -> ZF -> ZF  (* forall *)
    | ZF_Exists  : var -> Q -> ZF -> ZF. (* exists *)

  End OriginalForm.

  (* Semantics *)
  Section DirectSemantics.

    (* Definition of constant multiplication of natural numbers *)
    Fixpoint num_mult_nat (n : nat) (x : A) : A :=
      match n with
        | O   => Const0
        | S n => num_plus x (num_mult_nat n x)
      end.

    (* Definition of constant multiplication of integers *)
    Definition num_mult (z : Z) (exp : A) : A :=
      match z with
        | Z0     => Const0
        | Zpos x => num_mult_nat (nat_of_P x) exp
        | Zneg x => num_neg (num_mult_nat (nat_of_P x) exp)
      end.

    (* Substitution on Expressions *)
    Fixpoint subst_exp (p : var * A) (exp : ZExp) : ZExp :=
      match exp with
          ZExp_Var v     => if var_eq_dec (fst p) v then ZExp_Const (snd p) else exp
        | ZExp_Const _   => exp
        | ZExp_Add e1 e2 => ZExp_Add (subst_exp p e1) (subst_exp p e2)
        | ZExp_Inv e     => ZExp_Inv (subst_exp p e)
        | ZExp_Sub e1 e2 => ZExp_Sub (subst_exp p e1) (subst_exp p e2)
        | ZExp_Mult n e  => ZExp_Mult n (subst_exp p e)
      end.

    (* Substitution on Boolean Forms *)
    Fixpoint subst_bf (p : var * A) (bf : ZBF) : ZBF :=
      match bf with
          ZBF_Const _   => bf
        | ZBF_Lt e1 e2  => ZBF_Lt (subst_exp p e1) (subst_exp p e2)
        | ZBF_Lte e1 e2 => ZBF_Lte (subst_exp p e1) (subst_exp p e2)
        | ZBF_Gt e1 e2  => ZBF_Gt (subst_exp p e1) (subst_exp p e2)
        | ZBF_Gte e1 e2 => ZBF_Gte (subst_exp p e1) (subst_exp p e2)
        | ZBF_Eq e1 e2  => ZBF_Eq (subst_exp p e1) (subst_exp p e2)
        | ZBF_Eq_Max e1 e2 e3  => ZBF_Eq_Max (subst_exp p e1) (subst_exp p e2) (subst_exp p e3)
        | ZBF_Eq_Min e1 e2 e3  => ZBF_Eq_Min (subst_exp p e1) (subst_exp p e2) (subst_exp p e3)
        | ZBF_Neq e1 e2 => ZBF_Neq (subst_exp p e1) (subst_exp p e2)
      end.

    (* Substitution on Logic Forms *)
    Fixpoint substitute (p : var * A) (form : ZF) : ZF :=
      match form with
          ZF_BF bf      => ZF_BF (subst_bf p bf)
        | ZF_And f1 f2  => ZF_And (substitute p f1) (substitute p f2)
        | ZF_Or f1 f2   => ZF_Or (substitute p f1) (substitute p f2)
        | ZF_Imp f1 f2  => ZF_Imp (substitute p f1) (substitute p f2)
        | ZF_Not f      => ZF_Not (substitute p f)
        | ZF_Forall v q f => if var_eq_dec (fst p) v then form else ZF_Forall v q (substitute p f)
        | ZF_Exists v q f => if var_eq_dec (fst p) v then form else ZF_Exists v q (substitute p f)
      end.

    (* For the same variable, second substitution on expressions has no effect. *)
    Lemma same_var_subst_exp: forall exp v a1 a2, subst_exp (v, a1) (subst_exp (v, a2) exp) = subst_exp (v, a2) exp.
    Proof.
      induction exp; simpl; intros.
      destruct (var_eq_dec v0 v); simpl; auto.
      destruct (var_eq_dec v0 v); simpl; tauto.
      auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
    Qed.

    (* For the same variable, second substitution on boolean forms has no effect. *)
    Lemma same_var_subst_bf: forall bf v a1 a2, subst_bf (v, a1) (subst_bf (v, a2) bf) = subst_bf (v, a2) bf.
    Proof.
      destruct bf; simpl; intros; auto;
      try (rewrite same_var_subst_exp, same_var_subst_exp, same_var_subst_exp; auto);
      try (rewrite same_var_subst_exp, same_var_subst_exp; auto).
    Qed.

    (* For the same variable, second substitution on logic forms has no effect. *)
    Lemma same_var_subst: forall f v a1 a2, substitute (v, a1) (substitute (v, a2) f) = substitute (v, a2) f.
    Proof.
      induction f; intros;
      try (unfold substitute; rewrite same_var_subst_bf; auto);
      try (unfold substitute; fold substitute; rewrite IHf1, IHf2; auto);
      try (unfold substitute; fold substitute; rewrite IHf; auto);
      try (unfold substitute; fold substitute; unfold fst;
           destruct (var_eq_dec v0 v);
           unfold substitute; fold substitute; unfold fst;
           destruct (var_eq_dec v0 v); auto; try tauto;
           rewrite IHf; auto).
    Qed.

    (* Commutative law for substitution on expressions with different variables *)
    Lemma diff_var_subst_exp: forall exp v1 v2 a1 a2, v1 <> v2 -> subst_exp (v1, a1) (subst_exp (v2, a2) exp) =
                                                                  subst_exp (v2, a2) (subst_exp (v1, a1) exp).
    Proof.
      induction exp; simpl; intros.
      destruct (var_eq_dec v2 v), (var_eq_dec v1 v).
      rewrite <- e in e0; tauto.
      simpl; destruct (var_eq_dec v2 v); tauto.
      simpl; destruct (var_eq_dec v1 v); tauto.
      simpl. destruct (var_eq_dec v2 v), (var_eq_dec v1 v); tauto.
      auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
      rewrite IHexp1, IHexp2; auto.
      rewrite IHexp; auto.
    Qed.

    (* Commutative law for substitution on boolean forms with different variables *)
    Lemma diff_var_subst_bf: forall bf v1 v2 a1 a2, v1 <> v2 -> subst_bf (v1, a1) (subst_bf (v2, a2) bf) =
                                                                subst_bf (v2, a2) (subst_bf (v1, a1) bf).
    Proof.
      destruct bf; simpl; intros; auto;
      (rewrite diff_var_subst_exp  with (exp := z);
       try rewrite diff_var_subst_exp with (exp := z0);
       try rewrite diff_var_subst_exp with (exp := z1);
       auto).
    Qed.

    (* Commutative law for substitution on logic forms with different variables *)
    Lemma diff_var_subst: forall f v1 v2 a1 a2, v1 <> v2 -> substitute (v1, a1) (substitute (v2, a2) f) =
                                                            substitute (v2, a2) (substitute (v1, a1) f).
    Proof.
      induction f; intros;
      try (unfold substitute; rewrite diff_var_subst_bf; auto);
      try (unfold substitute; fold substitute; rewrite IHf1, IHf2; auto);
      try (unfold substitute; fold substitute; rewrite IHf; auto);
      (unfold substitute; fold substitute; unfold fst;
       destruct (var_eq_dec v2 v), (var_eq_dec v1 v); auto;
       try (rewrite <- e in e0; tauto);
       try (simpl; destruct (var_eq_dec v2 v), (var_eq_dec v1 v); try tauto);
       rewrite IHf; auto).
    Qed.

    (* Evaluation of Expressions *)
    Fixpoint dexp2ZE (exp : ZExp) : A :=
      match exp with
          ZExp_Var _     => Const0
        | ZExp_Const z   => z
        | ZExp_Add e1 e2 => num_plus (dexp2ZE e1) (dexp2ZE e2)
        | ZExp_Inv e     => num_neg (dexp2ZE e)
        | ZExp_Sub e1 e2 => num_plus (dexp2ZE e1) (num_neg (dexp2ZE e2))
        | ZExp_Mult z e  => num_mult z (dexp2ZE e)
      end.

    (* Evaluation of Boolean Forms *)
    Fixpoint dzbf2bool (bf : ZBF) : Val :=
      match bf with
          ZBF_Const b   => b
        | ZBF_Lt e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v1 v2) (truth_not (num_leq v2 v1))
        | ZBF_Lte e1 e2 => num_leq (dexp2ZE e1) (dexp2ZE e2)
        | ZBF_Gt e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v2 v1) (truth_not (num_leq v1 v2))
        | ZBF_Gte e1 e2 => num_leq (dexp2ZE e2) (dexp2ZE e1)
        | ZBF_Eq e1 e2  => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_and (num_leq v1 v2) (num_leq v2 v1)
        | ZBF_Eq_Max e1 e2 e3 =>
          let v1 := dexp2ZE e1 in
          let v2 := dexp2ZE e2 in
          let v3 := dexp2ZE e3 in
          truth_or (truth_and (num_leq v3 v2) (truth_and (num_leq v1 v2) (num_leq v2 v1)))
                   (truth_and (num_leq v2 v3) (truth_and (num_leq v1 v3) (num_leq v3 v1)))
        | ZBF_Eq_Min e1 e2 e3 =>
          let v1 := dexp2ZE e1 in
          let v2 := dexp2ZE e2 in
          let v3 := dexp2ZE e3 in
          truth_or (truth_and (num_leq v3 v2) (truth_and (num_leq v1 v3) (num_leq v3 v1)))
                   (truth_and (num_leq v2 v3) (truth_and (num_leq v1 v2) (num_leq v2 v1)))
        | ZBF_Neq e1 e2 => let v1 := dexp2ZE e1 in
                           let v2 := dexp2ZE e2 in
                           truth_not (truth_and (num_leq v1 v2) (num_leq v2 v1))
      end.

    (* Length of Logic Form *)
    Fixpoint length_zform (form : ZF) : nat :=
      match form with
          ZF_BF _       => 1
        | ZF_And f1 f2  => S (length_zform f1 + length_zform f2)
        | ZF_Or f1 f2   => S (length_zform f1 + length_zform f2)
        | ZF_Imp f1 f2  => S (length_zform f1 + length_zform f2)
        | ZF_Not f      => S (length_zform f)
        | ZF_Forall _ _ f => S (length_zform f)
        | ZF_Exists _ _ f => S (length_zform f)
      end.

    (* Substitution doesn't change the length *)
    Lemma substitute_length_inv : forall f x v, length_zform f = length_zform (substitute (v, x) f).
    Proof.
      induction f; simpl; try tauto; intros;
      try (rewrite <- IHf1; rewrite <- IHf2);
      try rewrite <- IHf;
      try (case (var_eq_dec v0 v); intros; simpl); auto.
    Defined.

    (* Definition of Validity of Logic Forms *)
    Inductive Input := Sat: ZF -> Input | DisSat: ZF -> Input | Udtmd: ZF -> Input.

    Definition length_input (inp : Input) :=
      match inp with
        | Sat f => length_zform f
        | DisSat f => length_zform f
        | Udtmd f => length_zform f
      end.

    Definition inputOrder (f1 f2 : Input) := length_input f1 < length_input f2.

    Lemma inputOrder_wf': forall len f, length_input f <= len -> Acc inputOrder f.
    Proof.
      unfold inputOrder; induction len; intros;
      [destruct f; destruct z; simpl in H; exfalso; intuition | constructor; intros; apply IHlen; omega].
    Defined.

    Theorem inputOrder_wf: well_founded inputOrder.
    Proof. red; intro; eapply inputOrder_wf'; eauto. Defined.

    Ltac smash := intros; unfold inputOrder; simpl; omega || rewrite <- substitute_length_inv; omega.

    Lemma sat_and_1: forall f1 f2, inputOrder (Sat f1) (Sat (ZF_And f1 f2)). smash. Defined.
    Lemma sat_and_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_And f1 f2)). smash. Defined.
    Lemma sat_or_1: forall f1 f2, inputOrder (Sat f1) (Sat (ZF_Or f1 f2)). smash. Defined.
    Lemma sat_or_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_Or f1 f2)). smash. Defined.
    Lemma sat_imp_1: forall f1 f2, inputOrder (DisSat f1) (Sat (ZF_Imp f1 f2)). smash. Defined.
    Lemma sat_imp_2: forall f1 f2, inputOrder (Sat f2) (Sat (ZF_Imp f1 f2)). smash. Defined.
    Lemma sat_not : forall f, inputOrder (DisSat f) (Sat (ZF_Not f)). smash. Defined.
    Lemma sat_forall:forall f v q(x:QT q),inputOrder(Sat (substitute (v, @conv q x) f))(Sat (ZF_Forall v q f)). smash. Defined.
    Lemma sat_exists:forall f v q(x:QT q),inputOrder(Sat (substitute (v, @conv q x) f))(Sat (ZF_Exists v q f)). smash. Defined.
    Lemma dst_and_1: forall f1 f2, inputOrder (DisSat f1) (DisSat (ZF_And f1 f2)). smash. Defined.
    Lemma dst_and_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_And f1 f2)). smash. Defined.
    Lemma dst_or_1: forall f1 f2, inputOrder (DisSat f1) (DisSat (ZF_Or f1 f2)). smash. Defined.
    Lemma dst_or_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_Or f1 f2)). smash. Defined.
    Lemma dst_imp_1: forall f1 f2, inputOrder (Sat f1) (DisSat (ZF_Imp f1 f2)). smash. Defined.
    Lemma dst_imp_2: forall f1 f2, inputOrder (DisSat f2) (DisSat (ZF_Imp f1 f2)). smash. Defined.
    Lemma dst_not : forall f, inputOrder (Sat f) (DisSat (ZF_Not f)). smash. Defined.
    Lemma dst_forall:forall f v q(x:QT q),inputOrder(DisSat(substitute (v,@conv q x) f))(Sat (ZF_Forall v q f)). smash. Defined.
    Lemma dst_exists:forall f v q(x:QT q),inputOrder(DisSat(substitute (v,@conv q x) f))(Sat (ZF_Exists v q f)). smash. Defined.
    Lemma udd_and_1 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_3 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_and_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_And f1 f2)). smash. Defined.
    Lemma udd_or_1 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_3 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_or_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_Or f1 f2)). smash. Defined.
    Lemma udd_imp_1 : forall f1 f2, inputOrder (DisSat f1) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_2 : forall f1 f2, inputOrder (Sat f2) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_3 : forall f1 f2, inputOrder (Sat f1) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_imp_4 : forall f1 f2, inputOrder (DisSat f2) (Udtmd (ZF_Imp f1 f2)). smash. Defined.
    Lemma udd_not_1 : forall f, inputOrder (DisSat f) (Udtmd (ZF_Not f)). smash. Defined.
    Lemma udd_not_2 : forall f, inputOrder (Sat f) (Udtmd (ZF_Not f)). smash. Defined.
    Lemma udd_forall_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Udtmd(ZF_Forall v q f)). smash. Defined.
    Lemma udd_forall_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Udtmd(ZF_Forall v q f)). smash. Defined.
    Lemma udd_exists_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Udtmd(ZF_Exists v q f)). smash. Defined.
    Lemma udd_exists_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Udtmd(ZF_Exists v q f)). smash. Defined.

    Definition three_pred : Input -> Prop :=
      Fix inputOrder_wf (fun _ => Prop)
          (fun (inp : Input) =>
             match inp return ((forall ff : Input, inputOrder ff inp -> Prop) -> Prop) with
               | Sat g =>
                 match g with
                   | ZF_BF bf      => fun _ => dzbf2bool bf = Top
                   | ZF_And f1 f2  => fun tpF => (tpF (Sat f1) (sat_and_1 f1 f2)) /\ (tpF (Sat f2) (sat_and_2 f1 f2))
                   | ZF_Or f1 f2   => fun tpF => (tpF (Sat f1) (sat_or_1 f1 f2)) \/ (tpF (Sat f2) (sat_or_2 f1 f2))
                   | ZF_Imp f1 f2  => fun tpF => (tpF (DisSat f1) (sat_imp_1 f1 f2)) \/ (tpF (Sat f2) (sat_imp_2 f1 f2))
                   | ZF_Not f      => fun tpF => (tpF (DisSat f) (sat_not f))
                   | ZF_Forall v q f => fun tpF => forall x: QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_forall f v q x))
                   | ZF_Exists v q f => fun tpF => exists x: QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_exists f v q x))
                 end
               | DisSat g =>
                 match g with
                   | ZF_BF bf => fun _ => dzbf2bool bf = Btm
                   | ZF_And f1 f2 => fun tpF => (tpF (DisSat f1) (dst_and_1 f1 f2)) \/ (tpF (DisSat f2) (dst_and_2 f1 f2))
                   | ZF_Or f1 f2 => fun tpF => (tpF (DisSat f1) (dst_or_1 f1 f2)) /\ (tpF (DisSat f2) (dst_or_2 f1 f2))
                   | ZF_Imp f1 f2 => fun tpF => (tpF (Sat f1) (dst_imp_1 f1 f2)) /\ (tpF (DisSat f2) (dst_imp_2 f1 f2))
                   | ZF_Not f => fun tpF => (tpF (Sat f) (dst_not f))
                   | ZF_Forall v q f => fun tpF => exists x : QT q,
                                                     (tpF (DisSat (substitute (v, @conv q x) f)) (dst_forall f v q x))
                   | ZF_Exists v q f => fun tpF => forall x : QT q,
                                                     (tpF (DisSat (substitute (v, @conv q x) f)) (dst_exists f v q x))
                 end
               | Udtmd g =>
                 match g with
                   | ZF_BF bf => fun _ => (dzbf2bool bf <> Top) /\ (dzbf2bool bf <> Btm)
                   | ZF_And f1 f2 => fun tpF => (~ ((tpF (Sat f1) (udd_and_1 f1 f2)) /\ (tpF (Sat f2) (udd_and_2 f1 f2)))) /\
                                                (~ ((tpF (DisSat f1) (udd_and_3 f1 f2)) \/ (tpF (DisSat f2) (udd_and_4 f1 f2))))
                   | ZF_Or f1 f2 => fun tpF => (~ ((tpF (Sat f1) (udd_or_1 f1 f2)) \/ (tpF (Sat f2) (udd_or_2 f1 f2)))) /\
                                               (~ ((tpF (DisSat f1) (udd_or_3 f1 f2)) /\ (tpF (DisSat f2) (udd_or_4 f1 f2))))
                   | ZF_Imp f1 f2 => fun tpF => (~ ((tpF (DisSat f1) (udd_imp_1 f1 f2)) \/ (tpF (Sat f2) (udd_imp_2 f1 f2)))) /\
                                                (~ ((tpF (Sat f1) (udd_imp_3 f1 f2)) /\ (tpF (DisSat f2) (udd_imp_4 f1 f2))))
                   | ZF_Not f => fun tpF => (~ ((tpF (DisSat f) (udd_not_1 f)))) /\ (~ ((tpF (Sat f) (udd_not_2 f))))
                   | ZF_Forall v q f =>
                     fun tpF => (~ (forall x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (udd_forall_1 f v q x)))) /\
                                (~ (exists x : QT q, (tpF (DisSat (substitute (v, @conv q x) f)) (udd_forall_2 f v q x))))
                   | ZF_Exists v q f =>
                     fun tpF => (~ (exists x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (udd_exists_1 f v q x)))) /\
                                (~ (forall x : QT q, (tpF (DisSat (substitute (v, @conv q x) f)) (udd_exists_2 f v q x))))
                 end
             end).
    Definition satisfied form := three_pred (Sat form).
    Definition dissatisfied form := three_pred (DisSat form).
    Definition undetermined form := three_pred (Udtmd form).

    Lemma satisfied_unfold :
      forall zf, satisfied zf = match zf with
                                  | ZF_BF bf      => (dzbf2bool bf = Top)
                                  | ZF_And f1 f2  => (satisfied f1) /\ (satisfied f2)
                                  | ZF_Or f1 f2   => (satisfied f1) \/ (satisfied f2)
                                  | ZF_Imp f1 f2  => (dissatisfied f1) \/ (satisfied f2)
                                  | ZF_Not f      =>  dissatisfied f
                                  | ZF_Forall v q f => forall x : QT q, (satisfied (substitute (v , @conv q x) f))
                                  | ZF_Exists v q f => exists x : QT q, (satisfied (substitute (v , @conv q x) f))
                                end.
    Proof.
      intro; unfold satisfied at 1; unfold three_pred; rewrite Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto); subst; destruct x]; auto.
    Qed.

    Lemma dissatisfied_unfold :
      forall zf, dissatisfied zf = match zf with
                                     | ZF_BF bf      => (dzbf2bool bf = Btm)
                                     | ZF_And f1 f2  => (dissatisfied f1) \/ (dissatisfied f2)
                                     | ZF_Or f1 f2   => (dissatisfied f1) /\ (dissatisfied f2)
                                     | ZF_Imp f1 f2  => (satisfied f1) /\ (dissatisfied f2)
                                     | ZF_Not f      => satisfied f
                                     | ZF_Forall v q f => exists x : QT q, (dissatisfied (substitute (v , @conv q x) f))
                                     | ZF_Exists v q f => forall x : QT q, (dissatisfied (substitute (v , @conv q x) f))
                                   end.
    Proof.
      intro; unfold dissatisfied at 1; unfold three_pred; rewrite Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto); subst; destruct x]; auto.
    Qed.

    Lemma undetermined_unfold : forall zf, undetermined zf <-> (~ satisfied zf) /\ (~ dissatisfied zf).
    Proof.
      intro; unfold undetermined at 1; unfold three_pred; rewrite satisfied_unfold, dissatisfied_unfold, Fix_eq;
      [destruct zf | intros; assert (HFunEq: f = g) by (extensionality a; extensionality b; auto); subst; destruct x]; intuition.
    Qed.

    Lemma sat_dissat_disj: forall zf, ~ (satisfied zf /\ dissatisfied zf).
    Proof.
      intro zf; remember (length_zform zf); assert (length_zform zf <= n) by omega; clear Heqn; revert zf H.
      induction n; intros.
      exfalso; destruct zf; simpl in H; intuition.
      destruct zf; rewrite satisfied_unfold, dissatisfied_unfold; intro SS; destruct SS; simpl in H.
      generalize bool_inj_not_eq; intro S; rewrite <- H0, <- H1 in S; apply S; trivial.
      destruct H0; destruct H1; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      destruct H1; destruct H0; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      rewrite <- dissatisfied_unfold in H0; rewrite dissatisfied_unfold in H1.
      destruct H1; destruct H0; [apply (IHn zf1) | apply (IHn zf2)]; intuition.
      rewrite <- dissatisfied_unfold in H0; rewrite dissatisfied_unfold in H1; apply (IHn zf); intuition.
      destruct H1; specialize (H0 x); apply (IHn (substitute (v, conv q x) zf)); [rewrite <- substitute_length_inv|]; intuition.
      destruct H0; specialize (H1 x); apply (IHn (substitute (v, conv q x) zf)); [rewrite <- substitute_length_inv|]; intuition.
    Qed.

    Lemma sat_undtmd_disj : forall zf, ~ (satisfied zf /\ undetermined zf).
    Proof. repeat intro; destruct H; rewrite undetermined_unfold in H0; destruct H0; apply H0; trivial. Qed.

    Lemma dissat_undtmd_disj : forall zf, ~ (dissatisfied zf /\ undetermined zf).
    Proof. repeat intro; destruct H; rewrite undetermined_unfold in H0; destruct H0; apply H1; trivial. Qed.

    Eval compute in satisfied (ZF_BF (ZBF_Const Btm)).

    Eval compute in satisfied (ZF_Or (ZF_BF (ZBF_Const Top)) (ZF_BF (ZBF_Const Btm))).

  End DirectSemantics.

  Section ZFWellFounded.

    Definition lengthOrder (f1 f2 : ZF) := length_zform f1 < length_zform f2.

    Lemma lengthOrder_wf': forall len f, length_zform f <= len -> Acc lengthOrder f.
    Proof.
      induction len; intros; destruct f;
      simpl in * |-; try omega;
      constructor; intros; unfold lengthOrder in * |-; simpl in * |-;
                                                                    apply IHlen with (f := y); omega.
    Defined.

    Theorem lengthOrder_wf: well_founded lengthOrder.
    Proof.
      red; intro; eapply lengthOrder_wf'; eauto.
    Defined.

    Ltac smash := intros; unfold lengthOrder; simpl; omega || rewrite <- substitute_length_inv; omega.

    Lemma lengthOrder_forall:forall f v q (x: QT q), lengthOrder (substitute (v, @conv q x) f) (ZF_Forall v q f). smash. Defined.
    Lemma lengthOrder_forall_trivial: forall f v q, lengthOrder f (ZF_Forall v q f). smash. Defined.
    Lemma lengthOrder_exists:forall f v q (x: QT q), lengthOrder (substitute (v, @conv q x) f) (ZF_Exists v q f). smash. Defined.
    Lemma lengthOrder_exists_trivial: forall f v q, lengthOrder f (ZF_Exists v q f). smash. Defined.
    Lemma lengthOrder_and_1: forall f1 f2, lengthOrder f1 (ZF_And f1 f2). smash. Defined.
    Lemma lengthOrder_and_2: forall f1 f2, lengthOrder f2 (ZF_And f1 f2). smash. Defined.
    Lemma lengthOrder_or_1: forall f1 f2, lengthOrder f1 (ZF_Or f1 f2). smash. Defined.
    Lemma lengthOrder_or_2: forall f1 f2, lengthOrder f2 (ZF_Or f1 f2). smash. Defined.
    Lemma lengthOrder_imp_1: forall f1 f2, lengthOrder f1 (ZF_Imp f1 f2). smash. Defined.
    Lemma lengthOrder_imp_2: forall f1 f2, lengthOrder f2 (ZF_Imp f1 f2). smash. Defined.
    Lemma lengthOrder_not: forall f, lengthOrder f (ZF_Not f). smash. Defined.

  End ZFWellFounded.

  Section Simplification.

    (* Elimination of Min and Max *)
    Definition eliminateMinMax (bf : ZBF) : ZF :=
      match bf with
          ZBF_Eq_Max e1 e2 e3 => ZF_Or (ZF_And (ZF_BF (ZBF_Eq e1 e2)) (ZF_BF (ZBF_Lte e3 e2)))
                                       (ZF_And (ZF_BF (ZBF_Eq e1 e3)) (ZF_BF (ZBF_Lte e2 e3)))
        | ZBF_Eq_Min e1 e2 e3 => ZF_Or (ZF_And (ZF_BF (ZBF_Eq e1 e2)) (ZF_BF (ZBF_Lte e2 e3)))
                                       (ZF_And (ZF_BF (ZBF_Eq e1 e3)) (ZF_BF (ZBF_Lte e3 e2)))
        | _ => ZF_BF bf
      end.

    (* Elimination of min and max doesn't change the validity of boolean forms *)
    Lemma eliminate_ok: forall z, (satisfied (ZF_BF z) <-> satisfied (eliminateMinMax z)) /\
                                   (dissatisfied (ZF_BF z) <-> dissatisfied (eliminateMinMax z)).
    Proof.
      split.
      destruct z; simpl; try tauto; repeat rewrite satisfied_unfold;
      simpl; rewrite truth_or_true_iff; repeat rewrite truth_and_true_iff; tauto.
      destruct z; simpl; try tauto; repeat rewrite dissatisfied_unfold;
      simpl; rewrite truth_or_false_iff; repeat rewrite truth_and_false_iff; tauto.
    Qed.

    Inductive SimpResult (f : ZF) :=
    | EQ_Top : f = ZF_BF (ZBF_Const Top) -> SimpResult f
    | EQ_Btm : f = ZF_BF (ZBF_Const Btm) -> SimpResult f
    | OTHER : f <> ZF_BF (ZBF_Const Top) /\ f <> ZF_BF (ZBF_Const Btm) -> SimpResult f.

    Definition judge (f : ZF) : SimpResult f.
      destruct f eqn : ?;
                         try (destruct z;
                              try (destruct (val_eq_dec v Top);
                                   [apply EQ_Top; rewrite e; trivial |
                                    destruct (val_eq_dec v Btm); [apply EQ_Btm; rewrite e; trivial |
                                                                  apply OTHER; split; intro; inversion H; contradiction]]);
                              apply OTHER; intuition; inversion H);
      apply OTHER; intuition; inversion H.
    Defined.

    (* Further Simplification: Elimination of boolean constants and min/max *)
    Fixpoint simplifyZF (form : ZF) : ZF :=
      match form with
          ZF_BF bf => eliminateMinMax bf
        | ZF_And f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                              e1, e2 =>
                              match (judge e1), (judge e2) with
                                | EQ_Top _, _ => e2
                                | _, EQ_Top _ => e1
                                | EQ_Btm _, _
                                | _, EQ_Btm _ => ZF_BF (ZBF_Const Btm)
                                | _, _ => ZF_And e1 e2
                              end
                          end
        | ZF_Or f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                             e1, e2 =>
                             match (judge e1), (judge e2) with
                               | EQ_Top _, _
                               | _, EQ_Top _ => ZF_BF (ZBF_Const Top)
                               | EQ_Btm _, _ => e2
                               | _, EQ_Btm _ => e1
                               | _, _ => ZF_Or e1 e2
                             end
                         end
        | ZF_Imp f1 f2 => match (simplifyZF f1), (simplifyZF f2) with
                              e1, e2 =>
                              match (judge e1), (judge e2) with
                                | EQ_Btm _, _
                                | _, EQ_Top _ => ZF_BF (ZBF_Const Top)
                                | EQ_Top _, EQ_Btm _ => ZF_BF (ZBF_Const Btm)
                                | EQ_Top _, _ => e2
                                | OTHER _, EQ_Btm _ => ZF_Not e1
                                | _, _ => ZF_Imp e1 e2
                              end
                          end
        | ZF_Not f => match (simplifyZF f) with
                          e => match (judge e) with
                                 | EQ_Top _ => ZF_BF (ZBF_Const Btm)
                                 | EQ_Btm _ => ZF_BF (ZBF_Const Top)
                                 | OTHER _ => ZF_Not e
                               end
                      end
        | ZF_Forall v q f => ZF_Forall v q (simplifyZF f)
        | ZF_Exists v q f => ZF_Exists v q (simplifyZF f)
      end.

  Ltac solve_bf_simp :=
    repeat match goal with
             | [|- _ /\ _ ] => split
             | [|- _ -> _ ] => intros
             | [z: ZBF, H : simplifyZF (ZF_BF ?z) = _ |- _] => destruct z; simpl in *
             | [H : ?X |- ?X] => apply H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _) |- _] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _) |- _] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _) |- _] => discriminate H
             | [|- exists e3 e4 : ZExp, ZF_BF (?X ?A ?B) = ZF_BF (?X e3 e4)] => exists A, B
             | [|- ?A = ?A] => auto
             | [H : forall (v : var) (q : Q) (x : QT q), _ , v : var, q : Q, x : QT _ |- _ ] =>
               specialize (H v q x); destruct H as [? [? [? [? [? [? ?]]]]]]
             | [H : simplifyZF (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?X with _ => _ end] |- _] => destruct (judge X)
             | [H1 : forall c : Val, simplifyZF ?f1 = ZF_BF (ZBF_Const c) -> _ ,
                  H2 : simplifyZF ?f1 = ZF_BF (ZBF_Const _) |- _] => specialize (H1 _ H2)
             | [|- simplifyZF (substitute _ (ZF_And _ _)) = _] => simpl
             | [|- context[match judge ?X with _ => _ end]] => destruct (judge X)
             | [H1: simplifyZF (substitute ?A ?f) = _, H2: simplifyZF (substitute ?A ?f) = _ |- _] =>
               rewrite H1 in *; clear H1
             | [H : ?A = ?B |- ?B = ?A ] => rewrite <- H; auto
             | [H : ZF_BF (ZBF_Const Top) = ZF_BF (ZBF_Const Btm) |- _] => inversion H; clear H
             | [H : ZF_BF (ZBF_Const Btm) = ZF_BF (ZBF_Const Top) |- _] => inversion H; clear H
             | [H : Top = Btm |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [H : Btm = Top |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [H : ?A = _ |- context[?A]] => rewrite H in *; clear H
             | [H : _ /\ _ |- _] => destruct H
             | [H : ?A <> ?A |- _] => exfalso; apply H; auto
             | [H1 : forall e1 e2 : ZExp, simplifyZF ?f = ZF_BF (?X e1 e2) -> exists e3 e4 : _ , _ ,
                  H2 : simplifyZF ?f = ZF_BF (?X _ _) |- exists e3 e4 : ZExp, _] =>
               let ee3 := fresh "ee3" in
               let ee4 := fresh "ee4" in
               specialize (H1 _ _ H2); destruct H1 as [ee3 [ee4 ?]]; exists ee3, ee4
             | [H : simplifyZF (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Or _ _)) = _] => simpl
             | [H : simplifyZF (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Imp _ _)) = _] => simpl
             | [H : ZF_Not _ = ZF_BF _ |- _] => discriminate H
             | [H : simplifyZF (ZF_Not _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Not _)) = _] => simpl
             | [H : simplifyZF (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Forall _ _ _)) = _] => simpl
             | [H : _ _ _ _ = ZF_BF _ |- _] => discriminate H
             | [H : simplifyZF (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [|- simplifyZF (substitute _ (ZF_Exists _ _ _)) = _] => simpl
           end.

  (* Substitution doesn't change the form of simplified result on boolean forms *)
  Lemma simp_subst_bf_same:
    forall f v q x,
      (forall c, simplifyZF f = ZF_BF (ZBF_Const c) -> simplifyZF (substitute (v, conv q x) f) = ZF_BF (ZBF_Const c)) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Lt e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Lt e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Lte e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Lte e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Gt e1 e2) ->
                     (exists e3 e4, simplifyZF (substitute (v,conv q x) f) = ZF_BF(ZBF_Gt e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Gte e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v,conv q x) f) = ZF_BF(ZBF_Gte e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Eq e1 e2) ->
                     (exists e3 e4, simplifyZF(substitute (v, conv q x) f) = ZF_BF (ZBF_Eq e3 e4))) /\
      (forall e1 e2, simplifyZF f = ZF_BF (ZBF_Neq e1 e2) ->
                     (exists e3 e4, simplifyZF (substitute (v, conv q x) f) = ZF_BF (ZBF_Neq e3 e4))).
  Proof. induction f; intros; solve_bf_simp. Qed.

  Ltac solve_eqminmax :=
    repeat match goal with
             | [|- eliminateMinMax ?z <> ZF_BF _] => destruct z; simpl; intuition
             | [|- context[match judge (simplifyZF ?f) with _ => _ end]] => destruct (judge (simplifyZF f))
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : forall e1 e2 e3 : ZExp, simplifyZF ?f <> ZF_BF (?X e1 e2 e3) |-
                                            simplifyZF ?f <> ZF_BF (?X _ _ _)] => apply H
             | [|- ZF_BF (_ _) <> ZF_BF (_ _ _ _)] => discriminate
             | [|- _ _ _ <> ZF_BF _] => discriminate
             | [|- _ _ _ _ <> ZF_BF _] => discriminate
             | [|- ZF_Not _ <> ZF_BF _] => discriminate
           end.

  (* Simplification really eliminates max. *)
  Lemma simp_no_eq_max : forall f e1 e2 e3, simplifyZF f <> ZF_BF (ZBF_Eq_Max e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  (* Simplification really eliminates min. *)
  Lemma simp_no_eq_min : forall f e1 e2 e3, simplifyZF f <> ZF_BF (ZBF_Eq_Min e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  Ltac solve_other_same :=
    repeat match goal with
             | [|- _ /\ _] => split
             | [|- _ -> _] => intros
             | [z : ZBF, H : simplifyZF (ZF_BF ?z) = _ |- _] => destruct z; simpl in H
             | [H : _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ |- _] => discriminate H
             | [H : ZF_BF _ = ZF_Not _ |- _] => discriminate H
             | [H : _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ _ |- _] => discriminate H
             | [|- context[simplifyZF (substitute _ (ZF_BF (ZBF_Eq_Max _ _ _)))]] => simpl
             | [|- context[simplifyZF (substitute _ (ZF_BF (ZBF_Eq_Min _ _ _)))]] => simpl
             | [|- exists f3 f4 : ZF, ?X ?A ?B = ?X f3 f4] => exists A, B; auto
             | [|- context[simplifyZF (substitute _ (ZF_And _ _))]] => simpl
             | [H : simplifyZF (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?A with _ => _ end] |- _] => destruct (judge A)
             | [|- context[match judge ?A with _ => _ end]] => destruct (judge A)
             | [H : _ /\ _ |- _ ] => destruct H
             | [H : simplifyZF ?f = ?X _ _,
                    H0 : forall f1 f3 : ZF,
                           simplifyZF ?f = ?X f1 f3 ->
                           exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5 |-
                                              exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5] =>
               let ff1 := fresh "ff1" in
               let ff2 := fresh "ff2" in
               specialize (H0 _ _ H); destruct H0 as [ff1 [ff2 ?]]; exists ff1, ff2; auto
             | [H : simplifyZF ?f = ?X _ _,
                    e1 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = _ _,
                         H0 : forall f1 f3 : ZF, simplifyZF ?f = ?X f1 f3 ->
                                                 exists f4 f5 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X f4 f5
                                                                    |- _] =>
               specialize (H0 _ _ H); destruct H0 as [? [? H0]]; rewrite H0 in e1; discriminate e1
             | [e : simplifyZF ?f = ZF_BF (ZBF_Const Top),
                    e0 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Btm) |- _] =>
               let H := fresh "H" in
               let S := fresh "S" in
               let M := fresh "M" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in e0; inversion e0 as [S];
               generalize bool_inj_not_eq; intro M; rewrite S in M; exfalso; apply M; auto
             | [e : simplifyZF ?f = ZF_BF (ZBF_Const Btm),
                    e0 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Top) |- _] =>
               let H := fresh "H" in
               let S := fresh "S" in
               let M := fresh "M" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in e0; inversion e0 as [S];
               generalize bool_inj_not_eq; intro M; rewrite S in M; exfalso; apply M; auto
             | [H : simplifyZF ?f = ZF_Not _,
                    e1 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF _,
                         H0 : forall f1 : ZF,
                                simplifyZF ?f = ZF_Not f1 ->
                                exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3
                                                |- _] =>
               specialize (H0 _ H); destruct H0 as [? H0]; rewrite H0 in e1; discriminate e1
             |[e : simplifyZF ?f = ZF_BF _, H : simplifyZF ?f = ZF_Not _ |- _] => rewrite H in e; discriminate e
             | [H : simplifyZF ?f = ZF_Not _,
                    H1 :
                  forall f2 : ZF,
                    simplifyZF ?f = ZF_Not f2 ->
                    exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3 |-
                                    exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_Not f3] =>
               let ff3 := fresh "ff3" in specialize (H1 _ H); destruct H1 as [ff3 ?]; exists ff3; auto
             |[ e : simplifyZF ?f = ZF_BF (ZBF_Const ?X),
                    H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let H := fresh "H" in
              destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ e); rewrite H in H2; exfalso; apply H2; auto
             |[H : forall (v : var) (q : Q) (x : QT q), _ |- context[(substitute (?v, conv ?q ?x) _)]] => specialize (H v q x)
             | [H : simplifyZF ?f = ?X _ _ _,
                    H4 : forall (v1 : var) (q1 : Q) (f1 : ZF),
                           simplifyZF ?f = ?X v1 q1 f1 ->
                           exists (v2 : var) (q2 : Q) (f3 : ZF),
                             simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X v2 q2 f3
                             |- exists (v2 : var) (q2 : Q) (f3 : ZF), simplifyZF (substitute (?v, conv ?q ?x) ?f) =
                                                                      ?X v2 q2 f3] =>
               let vv := fresh "vv" in
               let qq := fresh "qq" in
               let ff := fresh "ff" in
               specialize (H4 _ _ _ H); destruct H4 as [vv [qq [ff ?]]]; exists vv, qq, ff; apply H4
             | [H : simplifyZF ?f = ?X _ _ _,
                    H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = _ _,
                         H12 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                                 simplifyZF ?f = ?X v1 q1 f2 ->
                                 exists (v2 : var) (q2 : Q) (f3 : ZF),
                                   simplifyZF (substitute (?v, conv ?q ?x) ?f) = ?X v2 q2 f3 |- _ ] =>
               specialize (H12 _ _ _ H); destruct H12 as [? [? [? H12]]]; rewrite H12 in H2; discriminate H2
             |[ H2 : simplifyZF ?f <> ZF_BF (ZBF_Const ?X),
                     e : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const ?X) |- _] =>
              generalize (simp_subst_bf_same f v q x); intro; destruct (simplifyZF f) eqn : ?
             |[H10 : forall f2 f3 : ZF,
                       ?X ?z1 ?z2 = ?X f2 f3 ->
                       exists f4 f5 : ZF,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X f4 f5,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X z1 z2 = X z1 z2) by auto; specialize (H10 _ _ S);
              destruct H10 as [? [? ?]]; rewrite H10 in e; discriminate e
             |[H13 : forall f2 : ZF,
                       ZF_Not ?z = ZF_Not f2 ->
                       exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_Not f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] =>
              let S := fresh "S" in
              assert (S : ZF_Not z = ZF_Not z) by auto; specialize (H13 _ S);
              destruct H13 as [? ?]; rewrite H13 in e; discriminate e
             |[H14 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                       ?X ?v0 ?q0 ?z = ?X v1 q1 f2 ->
                       exists (v2 : var) (q2 : Q) (f3 : ZF),
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X v2 q2 f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X v0 q0 z = X v0 q0 z) by auto; specialize (H14 _ _ _ S);
              destruct H14 as [? [? [? H14]]]; rewrite H14 in e; discriminate e
             | [Heqz0 : simplifyZF ?f1 = _ _ _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [Heqz0 : simplifyZF ?f1 = _ _ _ _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [Heqz0 : simplifyZF ?f1 = ZF_Not _,
                        e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _,
                            IHf1 : forall (v : var) (q : Q) (x : QT q), _ |- _] => specialize (IHf1 v q x)
             | [z: ZBF, Heqz : simplifyZF ?f1 = ZF_BF _,
                               e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] => destruct z
             |[H17 : forall e1 e2 : ZExp,
                       ZF_BF (?X ?z ?z0) = ZF_BF (?X e1 e2) ->
                       exists e3 e4 : ZExp,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (?X e3 e4),
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const _) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H17 _ _ S);
              destruct H17 as [? [? H17]]; rewrite H17 in e; discriminate e
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Max ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_max f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Min ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_min f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[ H16 : forall c : Val,
                        ZF_BF (ZBF_Const ?v0) = ZF_BF (ZBF_Const c) ->
                        simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const c),
                  e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const ?X),
                  H2 : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (ZBF_Const v0) = ZF_BF (ZBF_Const v0)) by auto; specialize (H16 _ S);
              rewrite H16 in e; inversion e; rewrite e in H2; exfalso; apply H2; auto
             | [|- context[simplifyZF (substitute _ (ZF_Or _ _))]] => simpl
             | [H : simplifyZF (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Imp _ _))]] => simpl
             | [H : simplifyZF (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Not _))]] => simpl
             | [H : simplifyZF (ZF_Not _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Forall _ _ _))]] => simpl
             | [H : simplifyZF (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- context[simplifyZF (substitute _ (ZF_Exists _ _ _))]] => simpl
             | [H : simplifyZF (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [H : _ _ _ _ = ZF_Not _ |- _] => discriminate H
             |[|- exists (v2 : var) (q2 : Q) (f2 : ZF),
                    simplifyZF
                      (if var_eq_dec ?v0 ?v
                       then ?X ?v ?q ?f
                       else ?X ?v ?q (substitute (?v0, conv ?q0 ?x) ?f)) =
                    ?X v2 q2 f2] =>
              destruct (var_eq_dec v0 v); simpl;
              [exists v, q, (simplifyZF f) | exists v, q, (simplifyZF (substitute (v0, conv q0 x) f))]; auto
             |[|- exists f3 : ZF, ZF_Not ?A = ZF_Not f3] => exists A; auto
           end.

  (* Substitution doesn't change the form of simplified result on logic forms *)
  Lemma simp_subst_other_same:
    forall f v q x,
      (forall f1 f2, simplifyZF f = ZF_And f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_And f3 f4)) /\
      (forall f1 f2, simplifyZF f = ZF_Or f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_Or f3 f4)) /\
      (forall f1 f2, simplifyZF f = ZF_Imp f1 f2 -> (exists f3 f4, simplifyZF (substitute (v, conv q x) f) = ZF_Imp f3 f4)) /\
      (forall f1, simplifyZF f = ZF_Not f1 -> (exists f2, simplifyZF (substitute (v, conv q x) f) = ZF_Not f2)) /\
      (forall v1 q1 f1, simplifyZF f = ZF_Forall v1 q1 f1->
                        (exists v2 q2 f2, simplifyZF (substitute (v, conv q x) f) = ZF_Forall v2 q2 f2)) /\
      (forall v1 q1 f1, simplifyZF f = ZF_Exists v1 q1 f1->
                        (exists v2 q2 f2, simplifyZF (substitute (v, conv q x) f) = ZF_Exists v2 q2 f2)).
  Proof. induction f; intros; solve_other_same. Qed.

  Ltac solve_simp :=
    repeat match goal with
             | [|- context[match judge (simplifyZF ?A) with _ => _ end]] => destruct (judge (simplifyZF A))
             | [H : ?A = _ |- context[?A]] => rewrite H
             | [H : _ /\ _ |- _] => destruct H
             | [|- ?A = ?A] => auto
             | [|- substitute (_, conv _ _) (ZF_BF (ZBF_Const ?A)) = ZF_BF (ZBF_Const ?A)] => simpl; auto
             | [H : forall (v : var) (q : Q) (x : QT q),
                      substitute (v, conv q x) (simplifyZF ?f) = simplifyZF (substitute (v, conv q x) ?f) |-
                      context [substitute (?vv, conv ?qq ?xx) (simplifyZF ?f)]] => rewrite H
             | [|- substitute (_, conv _ _) (ZF_And _ _) = _] => simpl substitute at 1
             | [H1 : simplifyZF ?f = ZF_BF (ZBF_Const Top),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Btm) |- _ ]
               => let H := fresh "H" in
                  destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; clear H; inversion H2
             | [H : Btm = Top |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [H : Top = Btm |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [ H1 : simplifyZF ?f = ZF_BF (ZBF_Const ?X),
                      H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?X) |- _ ] =>
               let H := fresh "H" in
               destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; exfalso; apply H2; auto
             | [H1 : simplifyZF ?f = ZF_BF (ZBF_Const Btm),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const Top) |- _ ]
               => let H := fresh "H" in
                  destruct (simp_subst_bf_same f v q x) as [H _]; specialize (H _ H1); rewrite H in H2; clear H; inversion H2
             | [H : simplifyZF ?f = ZF_BF (ZBF_Const ?X) |-
                ZF_BF (ZBF_Const ?X) = simplifyZF (substitute (?v, conv ?q ?x) ?f)] =>
               let X := fresh "X" in
               destruct (simp_subst_bf_same f v q x) as [X _]; specialize (X _ H); rewrite X; auto
             | [H : simplifyZF ?f = ZF_BF (ZBF_Const ?X) |-
                substitute (?v, conv ?q ?x) (ZF_BF (ZBF_Const ?X)) = simplifyZF (substitute (?v, conv ?q ?x) ?f)] =>
               let X := fresh "X" in
               destruct (simp_subst_bf_same f v q x) as [X _]; specialize (X _ H); rewrite X; simpl; auto
             |[ H1 : simplifyZF ?f <> ZF_BF (ZBF_Const ?X),
                     H2 : simplifyZF (substitute (?v, conv ?q ?x) ?f) = ZF_BF (ZBF_Const ?X) |- _] =>
              generalize (simp_subst_bf_same f v q x); intro; generalize (simp_subst_other_same f v q x); intro;
              destruct (simplifyZF f) eqn : ?
             |[H10 : forall f2 f3 : ZF,
                       ?X ?z1 ?z2 = ?X f2 f3 ->
                       exists f4 f5 : ZF,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X f4 f5,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X z1 z2 = X z1 z2) by auto; specialize (H10 _ _ S);
              destruct H10 as [? [? ?]]; rewrite H10 in e; discriminate e
             |[H13 : forall f2 : ZF,
                       ZF_Not ?z = ZF_Not f2 ->
                       exists f3 : ZF, simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_Not f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] =>
              let S := fresh "S" in
              assert (S : ZF_Not z = ZF_Not z) by auto; specialize (H13 _ S);
              destruct H13 as [? ?]; rewrite H13 in e; discriminate e
             |[H14 : forall (v1 : var) (q1 : Q) (f2 : ZF),
                       ?X ?v0 ?q0 ?z = ?X v1 q1 f2 ->
                       exists (v2 : var) (q2 : Q) (f3 : ZF),
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ?X v2 q2 f3,
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = _ _ |- _] =>
              let S := fresh "S" in
              assert (S : X v0 q0 z = X v0 q0 z) by auto; specialize (H14 _ _ _ S);
              destruct H14 as [? [? [? H14]]]; rewrite H14 in e; discriminate e
             | [z: ZBF, Heqz : simplifyZF ?f1 = ZF_BF _,
                               e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF _ |- _] => destruct z
             |[H17 : forall e1 e2 : ZExp,
                       ZF_BF (?X ?z ?z0) = ZF_BF (?X e1 e2) ->
                       exists e3 e4 : ZExp,
                         simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (?X e3 e4),
                 e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const _) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H17 _ _ S);
              destruct H17 as [? [? H17]]; rewrite H17 in e; discriminate e
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Max ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_max f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[Heqz : simplifyZF ?f1 = ZF_BF (ZBF_Eq_Min ?z ?z0 ?z1) |- _] =>
              let S := fresh "S" in generalize (simp_no_eq_min f1 z z0 z1); intro S; rewrite Heqz in S; exfalso; apply S; auto
             |[ H16 : forall c : Val,
                        ZF_BF (ZBF_Const ?v0) = ZF_BF (ZBF_Const c) ->
                        simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const c),
                  e : simplifyZF (substitute (?v, conv ?q ?x) ?f1) = ZF_BF (ZBF_Const ?X),
                  H2 : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const ?X) |- _] =>
              let S := fresh "S" in
              assert (S : ZF_BF (ZBF_Const v0) = ZF_BF (ZBF_Const v0)) by auto; specialize (H16 _ S);
              rewrite H16 in e; inversion e; rewrite e in H2; exfalso; apply H2; auto
             | [|- context[substitute _ (ZF_And _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Or _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Imp _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Not _) ]] => simpl
             | [|- context[substitute _ (ZF_Forall _ _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Exists _ _ _) ]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplifyZF (ZF_Forall _ _ _)]] => simpl
             | [|- context[simplifyZF (ZF_Exists _ _ _)]] => simpl
           end.


  (* simplification and substitution are commutative. *)
  Lemma simp_subst_same: forall f v q x, substitute (v, conv q x) (simplifyZF f) = simplifyZF (substitute (v, conv q x) f).
  Proof. induction f; intros; simpl substitute at 2; simpl; try (destruct z; simpl; auto); solve_simp. Qed.

  Ltac solve_cnt :=
    repeat match goal with
             | [|- _ /\ _ ] => split
             | [z : ZBF, z0 : ZBF |- satisfied (ZF_BF ?z) /\ satisfied (ZF_BF ?z0) <-> _] => destruct z, z0
             | [z : ZBF, z0 : ZBF |- dissatisfied (ZF_BF ?z) \/ dissatisfied (ZF_BF ?z0) <-> _] => destruct z, z0
             | [|- context [match (judge ?X) with _ => _ end]] => destruct (judge X)
             | [e : ZF_BF ?X = ZF_BF (ZBF_Const _) |- context[ZF_BF ?X]] => rewrite e in *; clear e
             | [|- context[satisfied (ZF_BF (ZBF_Const Top))]] => rewrite satisfied_unfold; simpl
             | [|- context[satisfied (ZF_BF (ZBF_Const Btm))]] => rewrite satisfied_unfold; simpl
             | [|- context[dissatisfied (ZF_BF (ZBF_Const Top))]] => rewrite dissatisfied_unfold; simpl
             | [|- context[dissatisfied (ZF_BF (ZBF_Const Btm))]] => rewrite dissatisfied_unfold; simpl
             | [|- ?A = ?A /\ ?X <-> ?X] => intuition
             | [|- ?X /\ ?A = ?A <-> ?X] => intuition
             | [|- Btm = Top /\ _ <-> Btm = Top] => intuition
             | [|- ?X /\ Btm = Top <-> Btm = Top] => intuition
             | [|- Top = Btm \/ ?X <-> ?X] => intuition
             | [|- ?X \/ Top = Btm <-> ?X] => intuition
             | [|- ?X = ?X \/ _ <-> ?Y = ?Y ] => intuition
             | [|- _ \/ ?X = ?X <-> ?Y = ?Y ] => intuition
             | [|- Btm = Top \/ ?X <-> ?X] => intuition
             | [|- ?X \/ Btm = Top <-> ?X] => intuition
             | [|- Top = Btm /\ _ <-> Top = Btm] => intuition
             | [|- _ /\ Top = Btm <-> Top = Btm] => intuition
             | [|- Btm = Top /\ _ <-> Top = Btm] => intuition
             | [|- ?A = ?B <-> ?B = ?A] => intuition
             | [|- ?A = ?A <-> ?B = ?B] => intuition
             | [H : Btm = Top |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [H : Top = Btm |- _] => generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition
             | [|- satisfied ?A /\ satisfied ?B <-> satisfied (ZF_And ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A \/ dissatisfied ?B <-> dissatisfied (ZF_And ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [|- satisfied ?A \/ satisfied ?B <-> satisfied (ZF_Or ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A /\ dissatisfied ?B <-> dissatisfied (ZF_Or ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [|- dissatisfied ?A \/ satisfied ?B <-> satisfied (ZF_Imp ?A ?B)] =>
               split; intros; [rewrite satisfied_unfold | rewrite satisfied_unfold in * |-]; assumption
             | [|- satisfied ?X /\ ?A = ?A <-> dissatisfied (ZF_Not ?X)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; intuition
             | [|- satisfied ?A /\ dissatisfied ?B <-> dissatisfied (ZF_Imp ?A ?B)] =>
               split; intros; [rewrite dissatisfied_unfold | rewrite dissatisfied_unfold in * |-]; assumption
             | [e : ZF_BF (_ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion e
             | [e : ZF_BF (_ _ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion e
             | [e : _ _ _ = ZF_BF _ |- _] => inversion e
             | [e : ZF_Not _ = ZF_BF _ |- _] => inversion e
             | [e : _ _ _ _ = ZF_BF _ |- _] => inversion e
             | [|- dissatisfied ?A \/ Btm = Top <-> satisfied (ZF_Not ?A)] =>
               let H := fresh "H"
               in split; intro H;
                  [rewrite satisfied_unfold; destruct H as [H | H];
                   [assumption | generalize bool_inj_not_eq; intro; rewrite H in *; exfalso; intuition] |
                   rewrite satisfied_unfold in H; left; apply H]
             | [|- dissatisfied ?X <-> satisfied (ZF_Not ?X)] => rewrite satisfied_unfold; tauto
             | [|- satisfied ?X <-> dissatisfied (ZF_Not ?X)] => rewrite dissatisfied_unfold; tauto
           end.

  (* Simplification keeps the validity. *)
  Lemma simplify_ok: forall f, (satisfied f <-> satisfied (simplifyZF f)) /\
                               (dissatisfied f <-> dissatisfied (simplifyZF f)).
  Proof.
    intros; remember (length_zform f); assert (length_zform f <= n) by omega; clear Heqn; revert f H;
    induction n; intros.
    exfalso; destruct f; simpl in H; omega.
    destruct f; simpl.
    apply eliminate_ok.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    rewrite satisfied_unfold; rewrite dissatisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    rewrite satisfied_unfold; rewrite dissatisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [SAT1 DST1]; destruct (IHn _ S2) as [SAT2 DST2];
    split; [rewrite satisfied_unfold; rewrite DST1, SAT2 | rewrite dissatisfied_unfold; rewrite SAT1, DST2];
    clear H S1 S2 SAT1 SAT2 DST1 DST2 IHn n; destruct (simplifyZF f1), (simplifyZF f2); solve_cnt.

    simpl in H; apply le_S_n in H; assert (S : length_zform f <= n) by omega;
    destruct (IHn _ S) as [SAT DST]; split; [rewrite satisfied_unfold; rewrite DST | rewrite dissatisfied_unfold; rewrite SAT];
    clear H S SAT DST IHn n; destruct (simplifyZF f); solve_cnt.

    simpl in H; apply le_S_n in H; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold;
    split; split; intros; [| | destruct H0 as [x H0] | destruct H0 as [x H0]];
    assert (S : length_zform (substitute (v, conv q x) f) <= n) by (rewrite <- substitute_length_inv; assumption);
    destruct (IHn _ S) as [SAT DST];
    [rewrite simp_subst_same | rewrite <- simp_subst_same in SAT |
     exists x; rewrite simp_subst_same | exists x; rewrite <- simp_subst_same in DST]; intuition.

    simpl in H; apply le_S_n in H; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold;
    split; split; intros; [destruct H0 as [x H0] | destruct H0 as [x H0] | |];
    assert (S : length_zform (substitute (v, conv q x) f) <= n) by (rewrite <- substitute_length_inv; assumption);
    destruct (IHn _ S) as [SAT DST];
    [exists x; rewrite simp_subst_same | exists x; rewrite <- simp_subst_same in SAT |
            rewrite simp_subst_same | rewrite <- simp_subst_same in DST]; intuition.
  Qed.

  End Simplification.

End ArithSemantics.
