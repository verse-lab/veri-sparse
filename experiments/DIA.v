Set Implicit Arguments.
From LGTM.lib.theory Require Import LibFunExt LibLabType LibSummation LibSepTLCbuffer.
From LGTM.lib.seplog Require Import LibSepReference LibHypHeap LibWP LibXWP LibSepSimpl LibArray LibLoops Subst NTriple.
From LGTM.lib.theory Require Import LibListExt.
From LGTM.experiments Require Import Prelude UnaryCommon SV.
From mathcomp Require Import ssreflect ssrfun zify.
Hint Rewrite conseq_cons' : rew_listx.

Open Scope Z_scope.

Module dia.

Import sv.

Section dia.

Import List Vars list_interval_notation.

Notation "'diag_n'" := ("d_n_var":var) (in custom trm at level 0) : trm_scope.
Notation "'dind'" := ("d_ind":var) (in custom trm at level 0) : trm_scope.
Notation "'dval'" := ("d_val":var) (in custom trm at level 0) : trm_scope.
Notation "'ii'" := ("ii_'":var) (in custom trm at level 0) : trm_scope.
Notation "'col'" := ("col_'":var) (in custom trm at level 0) : trm_scope.
Notation "'ans'" := ("ans_'":var) (in custom trm at level 0) : trm_scope.

Context (dind dval : list int). (* Nonzero diag numbers, values on nonzero diags *)
Context (Ndiag Ndim : int). (* Number of nonzero diags, Dimentions of square matrix*)
Hypothesis Ndim_nonneg : 0 <= Ndim.
Hypothesis len_dind : length dind = Ndiag :> int.
Hypothesis dind_leq : forall x, In x dind -> 0 <= x < Ndim.
Hypothesis dind_weakly_sorted : forall (i j : int), 
  (0 <= i <= Ndim) -> 
  (0 <= j <= Ndim) -> 
  (i <= j) -> 
  (dind[i] <= dind[j]).

(* 
Due to the nature of the format there would be non-existing values 
in the enconding. It is impossible to access them from `dia_get` function, 
but `dia_sum` uses them. 

Thus it is required to specify that these values are all equal to zero.
*)
Hypotheses padding : forall (i : int),
  (i / Ndim - (i mod Ndim) >= Ndim \/ i / Ndim - (i mod Ndim) < 0) ->
  (dval[i] = 0).


Definition dia_get := 
<{
  fun dind dval i j  =>
    let "i bounded" = (i < Ndim) && (i >= 0) in
    let "j bounded" = (j < Ndim) && (j >= 0) in
    if "i bounded" && "j bounded" then     
        let k = i - j in 
        let ii = sv.indexf 0 Ndiag k dind in
        let "ii < bound" = ii < Ndiag in 
        if "ii < bound" then
            let col = dind[ii] in 
            dval[i + col*Ndim]
        else 
            0
    else 
        0
}>.


(* Definition dia_sum := 
<{
    fun dind dval => 
    let ans = ref 0 in
    for i <- [0, Ndim*Ndiag] { <- does not work due to index aligning in the proof
        let x = read_array dval i in
        ans += x
    };
    let "res" = !s in
    free ans;
    "res"
}>. *)

(* Seems too complex to handle properly *)
Definition dia_sum := 
<{
    fun dind dval => 
    let ans = ref 0 in
    for j <- [0, Ndiag] { 
        let diag_n = read_array dind j in 
        if diag_n < 0 then 
            for i <- [0, Ndim + diag_n] {
                let x = read_array dval i in
                ans += x    
            }
        else 
            for i <- [diag_n, Ndim]{
                let x = read_array dval i in
                ans += x    
            }
    };
    let "res" = !ans in
    free ans;
    "res"
}>.

Lemma dia_sum_spec {D : Type} `{Inhab D} (d_ind d_val : loc):
    {{
        arr(d_val, dval)⟨1, (0,0)⟩ \* (* connecting math array `dval` with pointer `d_val` for hyperindex ⟨1, (0,0)⟩ *)
        arr(d_ind, dind)⟨1, (0,0)⟩ \* (* connecting math array `dind` with pointer `d_ind` for hyperindex ⟨1, (0,0)⟩ *)
        (\*_(i <- `[0, Ndiag] \x `[0, Ndim]) arr(d_val, dval)⟨2, i⟩) \*
        (\*_(i <- `[0, Ndiag] \x `[0, Ndim]) arr(d_ind, dind)⟨2, i⟩)
        (* ^connecting representations with corresponding pointers for other indexes *)
    }}
    [{
        [1| ld in `{(0,0)} => dia_sum d_ind d_val];
        {2| ld in `[0, Ndim] \x `[0, Ndim] => dia_get d_ind d_val ld.1 ld.2}
    }]
    {{
     (*                     v- result in index(1 (0,0)) is equal to sum of results in hv(2, i ∈ [0, Ndim] × [0, Ndim]) *)
        hv, \[hv[`1]((0,0)) = Σ_(i <- `[0, Ndim] \x `[0, Ndim]) hv[`2](i)] \* \Top
     (* ^ heap vector? *)                                                   (* ^ Duplicates spatial precondition?? *) 
    }}.
    (* {{Arrs}} [{
        [1|      _ ∈ {0}                   => do dia_sum];
        [2| (i, j) ∈ [0, Ndim] × [0, Ndim] => get value by i and j];
    }] 
    {{ compare results from (1, (0,0)) with predifinded sum of individual values in (2, (i, j)) \* Arrs}}
    *)
Proof.
(* 
    At first let's unfold the dia_sum and look at the first component.

    {{Arrs}}
    [{
        1       : ans = ref 0; for-loop; ...return res
        2 (i, j): dia_get d_ind d_val i j
    }]{{
        a  | 
        el | ⌈a = Σᵢⱼ elᵢⱼ⌉ * 
           | Arrs
    }}

    applying SeqU1

    - case for 
        {{Arrs}} [{1: ans = ref 0 }] {{Arr * ans(1) -> 0}} <- solved with structural rules

    - {{Arrs * ans(1) -> 0}} [{
        1       : for-loop; ...return res
        2 (i, j): dia_get d_ind d_val i j
    }]
    }]{{
        a  | 
        el | ⌈a = Σᵢⱼ elᵢⱼ⌉ * 
           | Arrs
    }}

    applying SeqU2

    - case for free and return <- solved with structural rules

    - {{Arrs * ans(1) -> 0}} [{
        1       : for i <- [0, Ndim*Ndiag] {..}
        2 (i, j): dia_get d_ind d_val i j
    }]{{
        _  | ∃ v. ans(1) -> v *
        el | ⌈v = Σᵢⱼ elᵢⱼ⌉ * 
           | Arrs
    }}

    rewriting a bit 

    {{Arrs * ans(1) -> 0}} [{
        1       : for i <- [0, Ndim*Ndiag] {..}
        2 (i, j) i - j ∈ d_ind: dia_get d_ind d_val i j
        2 (i, j) i - j ∉ d_ind: dia_get d_ind d_val i j
    }]{{
        _  | ∃ v. ans(1) -> v *
        el | ⌈v = v₁ + v₂⌉ * 
           | ⌈v₁ = Σᵢⱼ elᵢⱼ, i - j ∈ d_ind⌉ *
           | ⌈v₂ = Σᵢⱼ elᵢⱼ, i - j ∉ d_ind⌉ *
           | Arrs
    }}

    applying Focus
    to split the indexes by those which are in d_ind and those which are not

    - First premise is proved by Fact 1 below.


    - {{Arrs * ans(1) -> 0}} [{
        1       : for i <- [0, Ndim*Ndiag] {..}
        2 (i, j) i - j ∈ d_ind: dia_get d_ind d_val i j
    }]{{
        _  | ∃ v. ans(1) -> v *
        el | ⌈v = v₁ + v₂⌉ * 
           | ⌈v₁ = Σᵢⱼ elᵢⱼ, i - j ∈ d_ind⌉ *
           | ⌈v₂ = 0⌉ *
           | Arrs
    }}

    simplifying remaning goal and framing out v₂ = 0

    {{Arrs * ans(1) -> 0}} [{
        1                     : for i <- [0, Ndim*Ndiag] {..}
        2 (i, j) i - j ∈ d_ind: dia_get d_ind d_val i j
    }]{{
        _  | ∃ v. ans(1) -> v *
        el | ⌈v = Σᵢⱼ elᵢⱼ, i - j ∈ d_ind⌉ * 
           | Arrs
    }}

-----------------I am stuck here----------    
?
?    As the dia matrix can be larger then its original, 
?    we need to extend get_dia function for the case, where
?    indecies are out of bounds. 
?
?    Should be doable by Frame Rule from SL
?
?    {{Arrs * ans(1) -> 0}} [{
?        1                     : for i <- [0, Ndim*Ndiag] {..}
?        2 (i, j) i - j ∈ d_ind: dia_get d_ind d_val i j
?        3 (i, j) ∈ [Ndim, 2*Ndim - 1] × [Ndim, 2*Ndim - 1]
?    }]{{
?        _  | ∃ v. ans(1) -> v *
?        el | ⌈v = Σᵢⱼ elᵢⱼ, i - j ∈ d_ind⌉ * 
?           | Arrs
?    }}
?
?
?    
?    applying For with
?        let i' = i % Ndim in
?        let k  = i / Ndim in
?
?        S(i) = {(2, i', i' - k)} <- the split is going to be by singleton indexes
?                                    those are to 
?        I(i, x el) = ans(1) -> Σ_(idx <- `[0, i'] \x `[0, j'])
?
?    - {{Arrs * ans(1) -> 0}}[{
?        1       : for i <- [0, Ndim*Ndiag] {..}
?        2 (i, j): dia_get d_ind d_val i j
?    }]
?
?
?
*)
Admitted.

(* 
Facts: 
1. about zero diagonals
{{
    Arrs
}}[{
    2 (i, j)_(i - j) ∉ d_ind: dia_get d_ind d_val i j
}]{{
    el | ∀ i, j: i - j ∉ d_ind elᵢⱼ = 0 * 
       | Arrs
}}

That can be rewritten as: 

{{
    Arrs
}}[{
    2 (i, j)_(i - j) ∉ d_ind: dia_get d_ind d_val i j
}]{{
    el | ∗_(i - j ∉ d_ind) ⌈elᵢⱼ = 0⌉ *
       | Arrs
}}

applying Product

{{
    Arrs * ⌈i - j ∉ d_ind⌉
}}[{
    2 (i, j): dia_get d_ind d_val i j
}]{{
    el | ⌈elᵢⱼ = 0⌉ *
       | Arrs
}}

This obligation can be discharged by employing index function specification.


 *)

