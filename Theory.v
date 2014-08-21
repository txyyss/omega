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
  Parameter truth_and : Val -> Val -> Val.
  Parameter truth_or : Val -> Val -> Val.
  Parameter truth_not : Val -> Val.
  Parameter bool_inj : bool -> Val.
  Axiom bool_inj_not_eq : bool_inj true <> bool_inj false.
  Axiom truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Axiom truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Axiom truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Axiom truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Axiom truth_or_true_iff : forall v1 v2, truth_or v1 v2 = bool_inj true <-> v1 = bool_inj true \/ v2 = bool_inj true.
  Axiom truth_and_true_iff : forall v1 v2, truth_and v1 v2 = bool_inj true <-> v1 = bool_inj true /\ v2 = bool_inj true.
End SEM_VAL.

Module Three_Val <: SEM_VAL.

  Inductive Val_Impl := VTrue | VFalse | VUnknown.
  Definition Val := Val_Impl.

  Definition bool_inj b :=
    match b with
      | true => VTrue
      | false => VFalse
    end.

  Lemma bool_inj_not_eq: bool_inj true <> bool_inj false.
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

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = bool_inj true <-> v1 = bool_inj true \/ v2 = bool_inj true.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H0. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = bool_inj true <-> v1 = bool_inj true /\ v2 = bool_inj true.
  Proof. intros; destruct v1, v2; simpl; intuition; inversion H. Qed.

End Three_Val.

Module Bool_Val <: SEM_VAL.
  Definition Val := bool.
  Definition truth_and := andb.
  Definition truth_or := orb.
  Definition truth_not := negb.
  Definition bool_inj b : bool := b.
  
  Lemma bool_inj_not_eq: bool_inj true <> bool_inj false. Proof. intro; inversion H. Qed.

  Lemma truth_and_comm : forall v1 v2, truth_and v1 v2 = truth_and v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_or_comm : forall v1 v2, truth_or v1 v2 = truth_or v2 v1.
  Proof. intros; destruct v1, v2; simpl; trivial. Qed.

  Lemma truth_and_assoc : forall v1 v2 v3, truth_and v1 (truth_and v2 v3) = truth_and (truth_and v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_assoc : forall v1 v2 v3, truth_or v1 (truth_or v2 v3) = truth_or (truth_or v1 v2) v3.
  Proof. intros; destruct v1, v2, v3; simpl; trivial. Qed.

  Lemma truth_or_true_iff : forall v1 v2, truth_or v1 v2 = bool_inj true <-> v1 = bool_inj true \/ v2 = bool_inj true.
  Proof. intros; unfold bool_inj; simpl; apply orb_true_iff. Qed.

  Lemma truth_and_true_iff : forall v1 v2, truth_and v1 v2 = bool_inj true <-> v1 = bool_inj true /\ v2 = bool_inj true.
  Proof. intros; unfold bool_inj; simpl; apply andb_true_iff. Qed.

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
  Definition num_leq (x y : A) := if Z_le_dec x y then bool_inj true else bool_inj false.
End FinLeqRelation.

Module Type NONE_RELATION (VAL : SEM_VAL).
  Import ZInfinity.
  Import VAL.
  Parameter none_leq : A -> Val.
  Parameter leq_none : A -> Val.
End NONE_RELATION.

Module None3ValRel <: NONE_RELATION Three_Val.
  Import ZInfinity Three_Val.
  Definition none_leq := fun _ : A => VUnknown.
  Definition leq_none := fun _ : A => VUnknown.
End None3ValRel.

Module NoneAlwaysFalse (VAL : SEM_VAL) <: NONE_RELATION VAL.
  Import ZInfinity VAL.
  Definition none_leq := fun _ : A => bool_inj false.
  Definition leq_none := fun _ : A => bool_inj false.
End NoneAlwaysFalse.

Module NoneAlwaysTrue (VAL : SEM_VAL) <: NONE_RELATION VAL.
  Import ZInfinity VAL.
  Definition none_leq := fun _ : A => bool_inj true.
  Definition leq_none := fun _ : A => bool_inj true.
End NoneAlwaysTrue.

Module InfLeqRelation (VAL : SEM_VAL) (S: NONE_RELATION VAL) <: LEQ_RELATION ZInfinity VAL.
  Import ZInfinity.
  Import VAL.
  Import S.
  (* Definition of relation "less than or equal to" *)
  Definition num_leq (ze1 ze2 : A) : Val :=
    match ze1, ze2 with
      | None, x                            => none_leq x
      | x, None                            => leq_none x
      | _, Some ZE_Inf                     => bool_inj true
      | Some ZE_NegInf, _                  => bool_inj true
      | Some ZE_Inf, Some x                => if ZE_eq_dec x ZE_Inf then bool_inj true else bool_inj false
      | Some x, Some ZE_NegInf             => if ZE_eq_dec x ZE_NegInf then bool_inj true else bool_inj false
      | Some (ZE_Fin z1), Some (ZE_Fin z2) => if Z_le_dec z1 z2 then bool_inj true else bool_inj false
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
  Inductive Input := Sat: ZF -> Input | DisSat: ZF -> Input | Undtmd: ZF -> Input.

  Definition length_input (inp : Input) :=
    match inp with
      | Sat f => length_zform f
      | DisSat f => length_zform f
      | Undtmd f => length_zform f
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
  Lemma udd_and_1 : forall f1 f2, inputOrder (Sat f1) (Undtmd (ZF_And f1 f2)). smash. Defined.
  Lemma udd_and_2 : forall f1 f2, inputOrder (Sat f2) (Undtmd (ZF_And f1 f2)). smash. Defined.
  Lemma udd_and_3 : forall f1 f2, inputOrder (DisSat f1) (Undtmd (ZF_And f1 f2)). smash. Defined.
  Lemma udd_and_4 : forall f1 f2, inputOrder (DisSat f2) (Undtmd (ZF_And f1 f2)). smash. Defined.
  Lemma udd_or_1 : forall f1 f2, inputOrder (Sat f1) (Undtmd (ZF_Or f1 f2)). smash. Defined.
  Lemma udd_or_2 : forall f1 f2, inputOrder (Sat f2) (Undtmd (ZF_Or f1 f2)). smash. Defined.
  Lemma udd_or_3 : forall f1 f2, inputOrder (DisSat f1) (Undtmd (ZF_Or f1 f2)). smash. Defined.
  Lemma udd_or_4 : forall f1 f2, inputOrder (DisSat f2) (Undtmd (ZF_Or f1 f2)). smash. Defined.
  Lemma udd_imp_1 : forall f1 f2, inputOrder (DisSat f1) (Undtmd (ZF_Imp f1 f2)). smash. Defined.
  Lemma udd_imp_2 : forall f1 f2, inputOrder (Sat f2) (Undtmd (ZF_Imp f1 f2)). smash. Defined.
  Lemma udd_imp_3 : forall f1 f2, inputOrder (Sat f1) (Undtmd (ZF_Imp f1 f2)). smash. Defined.
  Lemma udd_imp_4 : forall f1 f2, inputOrder (DisSat f2) (Undtmd (ZF_Imp f1 f2)). smash. Defined.
  Lemma udd_not_1 : forall f, inputOrder (DisSat f) (Undtmd (ZF_Not f)). smash. Defined.
  Lemma udd_not_2 : forall f, inputOrder (Sat f) (Undtmd (ZF_Not f)). smash. Defined.
  Lemma udd_forall_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Undtmd(ZF_Forall v q f)). smash. Defined.
  Lemma udd_forall_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Undtmd(ZF_Forall v q f)). smash. Defined.
  Lemma udd_exists_1:forall f v q(x:QT q),inputOrder(Sat(substitute(v,@conv q x)f))(Undtmd(ZF_Exists v q f)). smash. Defined.
  Lemma udd_exists_2:forall f v q(x:QT q),inputOrder(DisSat(substitute(v,@conv q x)f))(Undtmd(ZF_Exists v q f)). smash. Defined.
  
  Definition three_pred : Input -> Prop :=
    Fix inputOrder_wf (fun _ => Prop)
        (fun (inp : Input) =>
           match inp return ((forall ff : Input, inputOrder ff inp -> Prop) -> Prop) with
             | Sat g =>
               match g with
                 | ZF_BF bf      => fun _ => dzbf2bool bf = bool_inj true
                 | ZF_And f1 f2  => fun tpF => (tpF (Sat f1) (sat_and_1 f1 f2)) /\ (tpF (Sat f2) (sat_and_2 f1 f2))
                 | ZF_Or f1 f2   => fun tpF => (tpF (Sat f1) (sat_or_1 f1 f2)) \/ (tpF (Sat f2) (sat_or_2 f1 f2))
                 | ZF_Imp f1 f2  => fun tpF => (tpF (DisSat f1) (sat_imp_1 f1 f2)) \/ (tpF (Sat f2) (sat_imp_2 f1 f2))
                 | ZF_Not f      => fun tpF => (tpF (DisSat f) (sat_not f))
                 | ZF_Forall v q f => fun tpF => forall x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_forall f v q x))
                 | ZF_Exists v q f => fun tpF => exists x : QT q, (tpF (Sat (substitute (v, @conv q x) f)) (sat_exists f v q x))
               end
             | DisSat g =>
               match g with
                 | ZF_BF bf => fun _ => dzbf2bool bf = bool_inj false
                 | ZF_And f1 f2 => fun tpF => (tpF (DisSat f1) (dst_and_1 f1 f2)) \/ (tpF (DisSat f2) (dst_and_2 f1 f2))
                 | ZF_Or f1 f2 => fun tpF => (tpF (DisSat f1) (dst_or_1 f1 f2)) /\ (tpF (DisSat f2) (dst_or_2 f1 f2))
                 | ZF_Imp f1 f2 => fun tpF => (tpF (Sat f1) (dst_imp_1 f1 f2)) /\ (tpF (DisSat f2) (dst_imp_2 f1 f2))
                 | ZF_Not f => fun tpF => (tpF (Sat f) (dst_not f))
                 | ZF_Forall v q f => fun tpF => exists x : QT q,
                                                   (tpF (DisSat (substitute (v, @conv q x) f)) (dst_forall f v q x))
                 | ZF_Exists v q f => fun tpF => forall x : QT q,
                                                   (tpF (DisSat (substitute (v, @conv q x) f)) (dst_exists f v q x))
               end
             | Undtmd g =>
               match g with
                 | ZF_BF bf => fun _ => (dzbf2bool bf <> bool_inj true) /\ (dzbf2bool bf <> bool_inj false)
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
  Definition undetermined form := three_pred (Undtmd form).

  Lemma satisfied_unfold :
    forall zf, satisfied zf = match zf with
                                | ZF_BF bf      => (dzbf2bool bf = bool_inj true)
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
                                   | ZF_BF bf      => (dzbf2bool bf = bool_inj false)
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

  Eval compute in satisfied (ZF_BF (ZBF_Const (bool_inj false))).

  Eval compute in satisfied (ZF_Or (ZF_BF (ZBF_Const (bool_inj true))) (ZF_BF (ZBF_Const (bool_inj false)))).

End DirectSemantics.

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
  Lemma eliminate_ok: forall bf, satisfied (ZF_BF bf) <-> satisfied (eliminateMinMax bf).
  Proof.
    destruct bf; simpl; try tauto;
    repeat rewrite satisfied_unfold;
    simpl; rewrite truth_or_true_iff; repeat rewrite truth_and_true_iff; tauto.
  Qed.

End Simplification.

End ArithSemantics.
