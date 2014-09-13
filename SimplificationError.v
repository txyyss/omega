Require Import TheoryError.
Require Import TransformationError.
Require Import Bool.

Module SimplifyProof (sv:VARIABLE) (FZT : ZERO_FIN) (IZT : ZERO_INF).
  Module ThreeVSimp := ThreeValuedSimp sv FZT IZT.
  Import sv Three_Val_NoneError ThreeVSimp InfS FA PureInt.

  Ltac solve_eqminmax :=
    repeat match goal with
             | [|- eliminateMinMax ?z <> ZF_BF _] => destruct z; simpl; intuition
             | [|- context[match judge (simplify ?f) with _ => _ end]] => destruct (judge (simplify f))
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : forall e1 e2 e3 : ZExp, simplify ?f <> ZF_BF (?X e1 e2 e3) |-
                                            simplify ?f <> ZF_BF (?X _ _ _)] => apply H
             | [|- ZF_BF (_ _) <> ZF_BF (_ _ _ _)] => discriminate
             | [|- _ _ _ <> ZF_BF _] => discriminate
             | [|- _ _ _ _ <> ZF_BF _] => discriminate
             | [|- ZF_Not _ <> ZF_BF _] => discriminate
           end.

  (* Simplification really eliminates max. *)
  Lemma simp_no_eq_max : forall f e1 e2 e3, simplify f <> ZF_BF (ZBF_Eq_Max e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  (* Simplification really eliminates min. *)
  Lemma simp_no_eq_min : forall f e1 e2 e3, simplify f <> ZF_BF (ZBF_Eq_Min e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  Ltac solve_error :=
    match goal with
      | [H: forall _ _ , ?X ?z1 ?z2 = ?X _ _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 = X z1 z2) by auto; destruct (H _ _ S) as [? [? M]]; discriminate M
      | [H: forall _ , ZF_Not ?z1 = ZF_Not _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : ZF_Not z1 = ZF_Not z1) by auto; destruct (H _ S) as [? M]; discriminate M
      | [H: forall _ _ _, ?X ?z1 ?z2 ?z3 = ?X _ _ _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 z3 = X z1 z2 z3) by auto; destruct (H _ _ _ S) as [? [? [? M]]]; discriminate M
      | [z: ZBF, H: ZF_BF _ <> ZF_BF _ |- _] =>
        destruct z; match goal with
                      | [H : forall _ _, ZF_BF (?X ?z ?z0) = ZF_BF (?X _ _) -> _ |- _] =>
                        let S := fresh "S" in
                        let M := fresh "M" in
                        assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto;
                          destruct (H _ _ S) as [? [? M]]; discriminate M
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Max _ _ _) |- _] => exfalso; apply simp_no_eq_max in H; apply H
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Min _ _ _) |- _] => exfalso; apply simp_no_eq_min in H; apply H
                      | [H : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const _) |- _] =>
                        destruct v0; match goal with
                                       | [H : ?A <> ?A |- _] => exfalso; apply H; auto
                                       | [H1 : ?A <> ?B, H2: ?A = ?B |- _] => rewrite H2 in H1; exfalso; apply H1; auto
                                     end
                    end
    end.

  Ltac solve_impsb :=
    match goal with
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _ _,
                     ?X ?z1 ?z2 = ?X _ _ ->
                     exists _ _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ?X _ _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 = X z1 z2) by auto; specialize (H2 _ _ S); destruct H2 as [? [? M]];
        rewrite M in H1; discriminate H1
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _,
                     ZF_Not ?z1 = ZF_Not _ ->
                     exists _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_Not _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : ZF_Not z1 = ZF_Not z1) by auto; specialize (H2 _ S); destruct H2 as [? M];
        rewrite M in H1; discriminate H1
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _ _ _,
                     ?X ?z1 ?z2 ?z3 = ?X _ _ _ ->
                     exists _ _ _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ?X _ _ _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 z3 = X z1 z2 z3) by auto; specialize (H2 _ _ _ S); destruct H2 as [? [? [? M]]];
        rewrite M in H1; discriminate H1
      | [z: ZBF |- _] =>
        destruct z; match goal with
                      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const _),
                              H2 : forall _ _,
                                     ZF_BF (?X ?z ?z0) = ZF_BF (?X _ _) ->
                                     exists _ _,
                                       simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (?X _ _) |- _]
                        => let S := fresh "S" in
                           let M := fresh "M" in
                           assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H2 _ _ S);
                           destruct H2 as [? [? M]]; rewrite M in H1; discriminate H1
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Max _ _ _) |- _] => exfalso; apply simp_no_eq_max in H; apply H
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Min _ _ _) |- _] => exfalso; apply simp_no_eq_min in H; apply H
                      | [c: Val |- _] => destruct c; match goal with
                                                       | [H: ?A <> ?A |- _] => exfalso; apply H; trivial
                                                     end
                    end
    end.

  Ltac solve_same vv qq xx :=
    repeat match goal with
             | [|- _ /\ _] => split
             | [|- _ -> _ ] => intros
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_BF _ |- _] => destruct z; simpl in *
             | [H : ZF_BF (_ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion H
             | [H : ?X |- ?X] => apply H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _) |- _] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _) |- _] => discriminate H
             | [|- exists e3 e4 : ZExp, ZF_BF (?X ?A ?B) = ZF_BF (?X e3 e4)] => exists A, B
             | [|- ?A = ?A] => auto
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_And _ _ |- _] => destruct z; simpl in *
             | [H : _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ |- _] => discriminate H
             | [H : ZF_BF _ = ZF_Not _ |- _] => discriminate H
             | [H : ZF_Not _ = ZF_BF _ |- _] => discriminate H
             | [H : _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ _ = _ _ |- _] => discriminate H
             | [H : _ _ _ _ = _ _ _ |- _] => discriminate H
             | [H : ZF_Forall _ _ _ = ZF_Exists _ _ _ |- _] => discriminate H
             | [H : ZF_Exists _ _ _ = ZF_Forall _ _ _ |- _] => discriminate H
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Or _ _ |- _] => destruct z; simpl in *
             | [|- exists f3 f4 : ZF, ?X ?A ?B = ?X f3 f4] => exists A, B; auto
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Imp _ _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Not _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Forall _ _ _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Exists _ _ _ |- _] => destruct z; simpl in *
             | [H : forall (q : Q) (x : QT q) (v : var), _ |- _ ] =>
               specialize (H qq xx); destruct (H vv) as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]
             | [H : simplify (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?X with _ => _ end] |- _] => destruct (judge X)
             | [H1 : forall c : Val, simplify ?f1 = ZF_BF (ZBF_Const c) -> _ ,
                  H2 : simplify ?f1 = ZF_BF (ZBF_Const _) |- _] => specialize (H1 _ H2)
             | [|- simplify (substitute _ (ZF_And _ _)) = _] => simpl
             | [|- context[match judge ?X with _ => _ end]] => destruct (judge X)
             | [H1: simplify (substitute ?A ?f) = _, H2: simplify (substitute ?A ?f) = _ |- _] =>
               rewrite H1 in *
             | [H : ?A = ?B |- ?B = ?A ] => rewrite <- H; auto
             | [H : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VFalse) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VError) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VFalse) = ZF_BF (ZBF_Const VTrue) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VFalse) = ZF_BF (ZBF_Const VError) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VError) = ZF_BF (ZBF_Const VTrue) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VError) = ZF_BF (ZBF_Const VFalse) |- _] => discriminate H
             | [H : ?A = _ |- context[?A]] => rewrite H in *
             | [H : ?A = _, H2: context[?A] |- _] => rewrite H in *
             | [H : _ /\ _ |- _] => destruct H
             | [H : ?A <> ?A |- _] => exfalso; apply H; auto
             | [H : simplify ?f2 <> ZF_BF (ZBF_Const _), H2 : forall _ _, simplify ?f2 = ZF_And _ _ -> _ |- _] =>
               destruct (simplify f2) eqn: ?; solve_error
             | [|- context[simplify (substitute _ (ZF_And _ _))]] => simpl
             | [H : (forall _ _, ZF_BF (?X ?e1 ?e2) = ZF_BF (?X _ _) -> exists _ _, ?Y = ZF_BF (?X _ _))
                |- exists _ _, ?Y = ZF_BF (?X _ _)] =>
               let S := fresh "S" in assert (S : ZF_BF (X e1 e2) = ZF_BF (X e1 e2)) by auto; apply (H _ _ S)
             | [H : (forall _ _, ?X ?f0 ?f3 = ?X _ _ -> exists _ _, ?Y = ?X _ _) |- exists _ _, ?Y = ?X _ _]
               => let S := fresh "S" in assert (S : X f0 f3 = X f0 f3) by auto; apply (H _ _ S)
             | [H : (forall _, ?X ?f0 = ?X _ -> exists _, ?Y = ?X _) |- exists _, ?Y = ?X _]
               => let S := fresh "S" in assert (S : X f0 = X f0) by auto; apply (H _ S)
             | [H : (forall _ _ _, ?X ?f0 ?f3 ?f4 = ?X _ _ _ -> exists _ _ _, ?Y = ?X _ _ _)
                |- exists _ _ _, ?Y = ?X _ _ _]
               => let S := fresh "S" in assert (S : X f0 f3 f4 = X f0 f3 f4) by auto; apply (H _ _ _ S)
             | [H : simplify (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Or _ _))]] => simpl
             | [H : simplify (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Imp _ _))]] => simpl
             | [|- exists f3 : ZF, ZF_Not ?A = ZF_Not f3] => exists A; auto
             | [H : simplify (ZF_Not _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Not _))]] => simpl
             | [H : simplify (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Forall _ _ _))]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplify (ZF_Forall _ _ _)]] => simpl
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c), H : ZF_BF (ZBF_Const ?A) = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) = ZF_BF (ZBF_Const ?B), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; rewrite <- H in * |-; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const A) = ZF_BF (ZBF_Const A)) by auto; specialize (HC _ S);
               rewrite HC in e0; discriminate e0
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) <> ZF_BF (ZBF_Const ?c), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VTrue)) by auto;
               specialize (HC _ S); rewrite HC in e0; exfalso; apply e0; trivial
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) <> ZF_BF (ZBF_Const ?c), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const c) = ZF_BF (ZBF_Const c)) by auto;
               specialize (HC _ S); rewrite HC in e0; exfalso; apply e0; trivial
             | [|- exists (v2 : var) (q2 : Q) (f2 : ZF), ?X ?v1 ?q1 ?f1 = ?X v2 q2 f2] =>
               exists v1, q1, f1; trivial
             | [q : Q, q0 : Q, q1 : Q, H1: simplify (substitute (?v0, conv ?x) ?f) = ZF_BF (ZBF_Const ?A),
                                           H13 : simplify ?f <> ZF_BF (ZBF_Const ?A), IHf: forall _ : var, _ |- _] =>
               destruct q, q0, q1; destruct (IHf v0) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]];
               destruct (simplify f) eqn : ?; solve_impsb
             | [H : simplify (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Exists _ _ _))]] => simpl
             | [|- context[simplify (ZF_Exists _ _ _)]] => simpl
           end.

  (* Substitution doesn't change the form of simplified result *)
  Lemma simp_subst_the_same:
    forall f q (x : QT q) v,
      (forall c, simplify f = ZF_BF (ZBF_Const c) -> simplify (substitute (v, conv x) f) = ZF_BF (ZBF_Const c)) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Lt e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Lt e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Lte e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Lte e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Gt e1 e2) ->
                     (exists e3 e4, simplify (substitute (v,conv x) f) = ZF_BF(ZBF_Gt e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Gte e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Gte e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Eq e1 e2) ->
                     (exists e3 e4, simplify(substitute (v, conv x) f) = ZF_BF (ZBF_Eq e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Neq e1 e2) ->
                     (exists e3 e4, simplify (substitute (v, conv x) f) = ZF_BF (ZBF_Neq e3 e4))) /\
      (forall f1 f2, simplify f = ZF_And f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_And f3 f4)) /\
      (forall f1 f2, simplify f = ZF_Or f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_Or f3 f4)) /\
      (forall f1 f2, simplify f = ZF_Imp f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_Imp f3 f4)) /\
      (forall f1, simplify f = ZF_Not f1 -> (exists f2, simplify (substitute (v, conv x) f) = ZF_Not f2)) /\
      (forall v1 q1 f1, simplify f = ZF_Forall v1 q1 f1->
                        (exists v2 q2 f2, simplify (substitute (v, conv x) f) = ZF_Forall v2 q2 f2)) /\
      (forall v1 q1 f1, simplify f = ZF_Exists v1 q1 f1->
                        (exists v2 q2 f2, simplify (substitute (v, conv x) f) = ZF_Exists v2 q2 f2)).
  Proof. induction f; intros; solve_same v q x. Qed.

  (* simplification and substitution are commutative. *)
  Lemma simp_subst_comm: forall f v q (x : QT q), substitute (v, conv x) (simplify f) = simplify (substitute (v, conv x) f).
  Proof.
    induction f; intros; simpl substitute at 2; simpl; try (destruct z; simpl; auto);
    repeat match goal with
             | [|- context[match judge (simplify ?A) with _ => _ end]] => destruct (judge (simplify A))
             | [H : ?A = _ |- context[?A]] => rewrite H
             | [|- substitute (_, conv _) (ZF_BF (ZBF_Const ?A)) = ZF_BF (ZBF_Const ?A)] => simpl; auto
             | [H1: simplify ?f = ZF_BF (ZBF_Const _),
                    H2: simplify (substitute (?v, @conv ?q ?x) ?f) = ZF_BF (ZBF_Const _) |- _]
               => let H := fresh "H" in
                  destruct (simp_subst_the_same f q x v) as [H _]; specialize (H _ H1); rewrite H in H2; discriminate H2
             | [H : _ /\ _ |- _] => destruct H
             | [H1: simplify ?f = ZF_BF (ZBF_Const ?A),
                    H2: simplify (substitute (?v, @conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?A) |- _]
               => let H := fresh "H" in
                  destruct (simp_subst_the_same f q x v) as [H _]; specialize (H _ H1); rewrite H in H2; exfalso; apply H2; auto
             | [H1: simplify ?f <>ZF_BF(ZBF_Const ?A), H2:simplify (substitute (?v, @conv ?q ?x) ?f) = ZF_BF(ZBF_Const ?A) |- _]
               => destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]]; rewrite H2 in *;
                  destruct (simplify f) eqn : ?; solve_error
             | [H: forall _ _ _ , substitute _ (simplify ?f) = _ |- context[substitute _ (simplify ?f)]] => rewrite H
             | [|- ?A = ?A] => trivial
             | [|- context[substitute _ (ZF_And _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Or _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Imp _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Not _) ]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplify (ZF_Forall _ _ _)]] => simpl
             | [H1: ?A = _, H2: ?A = _ |- _] => rewrite H1 in H2
             | [H1: ?A = _, H2: ?A <> _ |- _] => rewrite H1 in H2
             | [H: ?A <> ?A |- _] => exfalso; apply H; trivial
             | [|- context[simplify (ZF_Exists _ _ _)]] => simpl
           end.
  Qed.

End SimplifyProof.