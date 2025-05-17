From Equations Require Import Equations.

Inductive expr :=
with subst :=
| S_id : subst
| S_shift : subst
| S_cons : expr -> subst -> subst
| S_comp : subst -> subst -> subst.

Equations f : subst -> subst -> subst :=
f (S_comp S_shift s1) _ := s1 ;
f s1 s2 := S_comp s1 s2.

Lemma f_incorrect s1 s2 : 
  f (S_comp S_id s1) s2 = S_comp (S_comp S_id s1) s1.
Proof. reflexivity. Qed.

Equations g : subst -> subst -> subst :=
g (S_comp S_shift s1) _ := s1 ;
g x y := S_comp x y.

Lemma g_correct s1 s2 : 
  g (S_comp S_id s1) s2 = S_comp (S_comp S_id s1) s2.
Proof. reflexivity. Qed.



