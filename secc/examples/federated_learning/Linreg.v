Require Import 
  Coq.QArith.QArith Reals
  Lia Vector CoLoR.Util.Vector.VecUtil
  Coquelicot.Coquelicot Psatz.
Import VectorNotations.

Open Scope R_scope.


Definition flinreg (m c : R) (x : R) := m * x + c.

Check (fun m c => Derive (fun x => flinreg x m c) m).
Print Derive.


(* We compute the yhat *)
Definition compute_yhat {n : nat} (m c : R) (xs : Vector.t R n) : Vector.t R n :=
  Vmap (fun t => flinreg m c t) xs.

Definition zip_with : forall {n : nat}, (R -> R -> R) ->  
  Vector.t R n -> Vector.t R n -> Vector.t R n.
  induction n.
  + intros f u v. 
    exact Vnil. 
  + intros f u v. 
    exact (Vcons (f (Vhead u) (Vhead v)) (IHn f (Vtail u) (Vtail v))).
Defined.

Definition sum_vec {n : nat} (xs : Vector.t R n) := 
  Vfold_left (fun x y => x + y) R0 xs.


Definition mean_of_square_error {n : nat} (xs ys : Vector.t R n) (m c : R) : R :=  
  Rdiv (sum_vec (zip_with (fun x y => (m * x + c - y) ^ 2) xs ys)) (INR n).


Lemma is_differentiable_c : forall (n : nat) (xs ys : Vector.t R n) (m c : R), 
  is_derive (mean_of_square_error xs ys m) c 
   (Rdiv (sum_vec (zip_with (fun x y => 2 * (m * x + c - y)) xs ys)) (INR n)).
Proof.
  intros.
  evar_last.
  
Admitted.


Lemma is_differentiable_m : forall (n : nat) (xs ys : Vector.t R n) (m c : R), 
  is_derive (fun m' => mean_of_square_error xs ys m' c) m 
   (Rdiv (sum_vec (zip_with (fun x y => 2 * (m * x + c - y) * x) xs ys)) (INR n)).
Proof.
  intros.



Admitted.

(*
Eval compute in (zip (fun x y => x + y) (Vcons 1 (Vcons 2 Vnil)) (Vcons 2 (Vcons 3 Vnil))).
*)









