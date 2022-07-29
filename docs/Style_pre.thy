(*
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
*)

theory Style_pre
  imports Main
begin

text \<open>
This a helper theory for Style.thy.
\<close>

typedecl type_foo
typedecl type_bar

definition valid ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
  where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> undefined"

definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
  where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

consts my_function :: 'a
axiomatization where my_function_def: "my_function \<equiv> undefined"

definition ccorres :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> bool" where
  "ccorres rrel xf P Q hs a c \<equiv> undefined"

consts rrel :: 'a
axiomatization where rrel_def: "rrel \<equiv> undefined"

consts xf :: 'b
axiomatization where xf_def: "xf \<equiv> undefined"

consts short_abs_guard :: 'c
axiomatization where short_abs_guard_def: "short_abs_guard \<equiv> undefined"

consts long_abs_guard :: 'c
axiomatization where long_abs_guard_def: "long_abs_guard \<equiv> undefined"

consts short_conc_guard :: 'd
axiomatization where short_conc_guard_def: "short_conc_guard \<equiv> undefined"

consts long_conc_guard :: 'd
axiomatization where long_conc_guard_def: "long_conc_guard \<equiv> undefined"

consts hs :: 'e
axiomatization where hs_def: "hs \<equiv> undefined"

consts short_abs_fn :: 'f
axiomatization where short_abs_fn_def: "short_abs_fn \<equiv> undefined"

consts long_abs_fn :: 'f
axiomatization where long_abs_fn_def: "long_abs_fn \<equiv> undefined"

consts short_conc_fn :: 'g
axiomatization where short_conc_fn_def: "short_conc_fn \<equiv> undefined"

consts long_conc_fn :: 'g
axiomatization where long_conc_fn_def: "long_conc_fn \<equiv> undefined"

consts UNIV :: 'd
axiomatization where UNIV_def: "UNIV \<equiv> undefined"

definition c_guard :: "'h \<Rightarrow> 'i \<Rightarrow> 'd" ("\<lbrace> _ = _ \<rbrace>") where
  "\<lbrace> ptr = cond \<rbrace> \<equiv> undefined"

definition ptr_select :: "'h \<Rightarrow> 'h" ("\<acute>") where
  "ptr_select \<equiv> undefined"

consts ptr :: 'h
axiomatization where ptr_def: "ptr \<equiv> undefined"

consts cond :: 'i
axiomatization where cond_def: "cond \<equiv> undefined"

end
