theory Queue
imports Main
begin

datatype 'a List = N | C 'a "'a List"

fun app :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "app N ys = ys" |
  "app (C x xs) ys = C x (app xs ys)"

fun reverse :: "'a List \<Rightarrow> 'a List" where
  "reverse N = N" |
  "reverse (C x xs) = app (reverse xs) (C x N)"


value "reverse (C a (C b (C c N)))"

lemma app_n [simp]: "app xs N = xs"
  apply (induction xs)
  apply auto
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply auto
  done

lemma reverse_app [simp]: "reverse (app xs ys) = app (reverse ys) (reverse xs)"
  apply (induction xs)
  apply auto
  done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto
  done

export_code reverse in Haskell module_name List

datatype 'a AQueue = AQueue "'a List" "'a List"

definition emptyQ :: "'a AQueue" where
  [simp]:"emptyQ = AQueue N N"

fun enqueue :: "'a \<Rightarrow> 'a AQueue \<Rightarrow> 'a AQueue" where
  "enqueue x (AQueue xs ys) = AQueue (C x xs) ys"

fun dequeue :: "'a AQueue \<Rightarrow> 'a option \<times> 'a AQueue" where
  "dequeue (AQueue N N) = (None, AQueue N N)"
 |"dequeue (AQueue xs (C y ys)) = (Some y, AQueue xs ys)"
(* |"dequeue (AQueue xs N) = dequeue (AQueue N (reverse xs))" *)
 |"dequeue (AQueue xs N) = (case reverse xs of C y ys \<Rightarrow> (Some y, AQueue N ys))"

export_code enqueue dequeue in Haskell module_name Queue

fun fast_rev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "fast_rev N ys = ys"
| "fast_rev (C x xs) ys = fast_rev xs (C x ys)"

lemma [simp]: "fast_rev xs ys = app (reverse xs) ys"
  apply (induction xs arbitrary: ys)
  apply auto
  done

lemma [code_unfold]: "reverse xs = fast_rev xs N"
  apply auto
  done

lemma app_eq_N[simp]: "app xs ys = N \<longleftrightarrow> xs = N \<and> ys = N"
  apply (induct xs)
  apply auto
  done

fun list_of :: "'a AQueue \<Rightarrow> 'a List" where
  "list_of (AQueue xs ys) = (app xs (reverse ys))"

definition empty' :: "'a List" where
  [simp]: "empty' = N"

fun enqueue' :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "enqueue' x xs = C x xs"

fun dequeue' :: "'a List \<Rightarrow> 'a option \<times> 'a List" where
  "dequeue' xs = (case reverse xs of N \<Rightarrow> (None, N)
                                   | C x xs \<Rightarrow> (Some x, reverse xs))"

lemma list_of_empty: "list_of emptyQ = empty'"
  apply auto
  done

lemma list_of_enqueue: "list_of (enqueue x q) = enqueue' x (list_of q)"
  apply (induction q)
  apply auto
  done

lemma list_of_dequeue1: "fst (dequeue q) = fst (dequeue' (list_of q))"
  apply (induction q rule: dequeue.induct)
  apply (auto split: List.split)
  done

lemma list_of_dequeue2: "list_of (snd (dequeue q)) = snd (dequeue' (list_of q))"
  apply (induction q rule: dequeue.induct)
  apply (auto split: List.split)
  done

export_code enqueue dequeue in Haskell module_name Queue

end
