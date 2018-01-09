(*formal semantics of brainfuck*)

theory brainfuck_semantics
imports Main
  "~~/src/HOL/Word/Word"
begin

type_synonym byte = "8 word"
lemma "(256 :: byte) = 0" by simp


datatype bf_cmd = BF_RIGHT --">, increment the data pointer (to point to the next cell to the right)." 
                | BF_LEFT --"<, decrement the data pointer (to point to the next cell to the left)."
                | BF_PLUS  --"+, increment the byte at the data pointer."
                | BF_MINUS --"-, decrement the byte at the data pointer."
                | BF_OUTPUT --"., output the byte at the data pointer."
                | BF_INPUT --",, accept one byte of input, storing its value in the byte at the data pointer."
                | BF_LOOP bf_cmd  --"[ \<dots> ], while data pointer is not zero"
                | BF_SEQ bf_cmd bf_cmd --"Doesn't esist in brainfuck, but makes defining a semantics so much easier,
                  because lists are not required to compose programs"
                | BF_NOOP --"dito"
                  
abbreviation c_RIGHT ("\<^bold>< _" ) where "c_RIGHT l \<equiv> BF_SEQ BF_RIGHT l"
abbreviation c_LEFT ("\<^bold>> _") where "c_LEFT l \<equiv> BF_SEQ BF_LEFT l"
abbreviation c_PLUS ("\<^bold>+ _") where "c_PLUS l \<equiv> BF_SEQ BF_PLUS l"
abbreviation c_MINUS ("\<^bold>- _") where "c_MINUS l \<equiv> BF_SEQ BF_MINUS l"
abbreviation c_OUTPUT ("\<^bold>. _") where "c_OUTPUT l \<equiv> BF_SEQ BF_OUTPUT l"
abbreviation c_INPUT ("\<^bold>, _") where "c_INPUT l \<equiv> BF_SEQ BF_INPUT l"
abbreviation c_LOOP ("\<^bold>[ _ \<^bold>] _") where "c_LOOP i l \<equiv> BF_SEQ (BF_LOOP i) l"
abbreviation c_END ("\<box>") where "\<box> \<equiv> BF_NOOP"


  
datatype tape = Tape "byte list" byte    "byte list"
--"                   left       current right"
--" left is ordered in reverse"
--"tape is (rev left)@[current]@right"
definition "initial_tape \<equiv> Tape [] 0 []"

datatype outp = Outp "byte list"
datatype inp = Inp "byte list"
datatype state = Normal tape inp outp
definition "initial_state inp \<equiv> Normal initial_tape (Inp inp) (Outp [])"
definition "s_tape state \<equiv> (case state of Normal tape _ _ \<Rightarrow> case tape of Tape l c r \<Rightarrow> c)"
lemmas initial_state_def[simp] initial_tape_def[simp] s_tape_def[simp]

inductive eval_bf :: "bf_cmd \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"  where
init:  "s = s' \<Longrightarrow> eval_bf BF_NOOP s s'" |
 "eval_bf BF_RIGHT (Normal (Tape lt c []) inp outp)       (Normal (Tape (c#lt) 0 []) inp outp)" |
 "eval_bf BF_RIGHT (Normal (Tape lt c (rt#rts)) inp outp) (Normal (Tape (c#lt) rt rts) inp outp)" |
 "eval_bf BF_LEFT  (Normal (Tape [] c rt) inp outp)       (Normal (Tape [] 0 (c#rt)) inp outp)"  | (* debatable, but definitely less annoying than some error state *)
 "eval_bf BF_LEFT  (Normal (Tape (lt#lts) c rt) inp outp) (Normal (Tape lts lt (c#rt)) inp outp)" |
 "eval_bf BF_PLUS  (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c + 1) rt) inp outp)" |
 "eval_bf BF_MINUS (Normal (Tape lt c rt) inp outp)       (Normal (Tape lt (c - 1) rt) inp outp)" |
 "eval_bf BF_OUTPUT (Normal (Tape lt c rt) inp (Outp outp))     (Normal (Tape lt c rt) inp (Outp (c#outp)))" |
 "eval_bf BF_INPUT  (Normal (Tape lt _ rt) (Inp []) outp)       (Normal (Tape lt 0 rt) (Inp []) outp)" |
 "eval_bf BF_INPUT  (Normal (Tape lt _ rt) (Inp (i#is)) outp)   (Normal (Tape lt i rt) (Inp is) outp)" |
seq:   "eval_bf code s s' \<Longrightarrow> eval_bf code' s' s'' \<Longrightarrow> eval_bf (BF_SEQ code code') s s''" | (* bigstep *)
whileTrue:  "c \<noteq> 0 \<Longrightarrow> eval_bf code (Normal (Tape lt c rt) inp outp) s\<^sub>1 \<Longrightarrow> eval_bf (BF_LOOP code)  s\<^sub>1 s\<^sub>2 \<Longrightarrow>
              eval_bf (BF_LOOP code)  (Normal (Tape lt c rt) inp outp) s\<^sub>2" |
whileFalse: "eval_bf (BF_LOOP code) (Normal (Tape lt 0 rt) inp outp) (Normal (Tape lt 0 rt) inp outp)"

(* Note that it is very elegant to roll with something like
type_synonym tape = "int \<Rightarrow> byte"
definition "initial_tape :: tape \<equiv> \<lambda>_. 0" -- "Current cell is always tape 0"
 "eval_bf BF_RIGHT  (Normal tape inp outp)          (Normal (\<lambda>c. tape (c - 1)) inp outp)" |
 "eval_bf BF_LEFT   (Normal tape inp outp)          (Normal (\<lambda>c. tape (c + 1)) inp outp)"  |
 "eval_bf BF_PLUS   (Normal tape inp outp)          (Normal (tape(0 := tape 0 + 1)) inp outp)" |
 "eval_bf BF_MINUS  (Normal tape inp outp)          (Normal (tape(0 := tape 0 - 1)) inp outp)" |
it is also too inefficient
(Peter would probably automatically refine me for this statement) *)

lemmas eval_bf.intros(1-11,13)[intro!]

code_pred (modes: i => i => o => bool as compute_bf) eval_bf .
    
lemma noope[simp,dest]: "eval_bf \<box> s t \<Longrightarrow> s = t"
  by(cases "\<box>" s t rule: eval_bf.cases)
    
lemma seq_eq: "eval_bf (BF_SEQ c d) s t = (\<exists>i. eval_bf c s i \<and> eval_bf d i t)"
  apply(rule iffI)
  subgoal
    apply(cases "(BF_SEQ c d)" s t rule: eval_bf.cases; assumption?)
    apply blast
    done
  subgoal
    apply(elim exE conjE)
    apply(rule seq)
     apply(assumption)+
    done
  done
    

lemma unbox[simp]: 
  "eval_bf (BF_SEQ c \<box>) s t = eval_bf c s t" 
  "eval_bf (BF_SEQ \<box> c) s t = eval_bf c s t"
  by(auto simp add: seq_eq)

    
lemma seq_while_split: "eval_bf (\<^bold>[ c \<^bold>] \<box>) s si \<Longrightarrow> eval_bf (c') si s'
   \<Longrightarrow> eval_bf (\<^bold>[ c \<^bold>] c') s s'"
  by (simp add: seq)

lemma "eval_bf (\<^bold>+\<^bold>.\<box>) (initial_state inp) (Normal (Tape [] 1 []) (Inp inp) (Outp [1]))"
  by auto

value "bf_hello_world"
definition "bf_hello_world \<equiv>  \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+
\<^bold>[ \<^bold>< \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>< \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>< \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>< \<^bold>+ \<^bold>> \<^bold>> \<^bold>> \<^bold>> \<^bold>- \<box> \<^bold>] 
\<^bold>< \<^bold>+ \<^bold>+ \<^bold>.
\<^bold>< \<^bold>+ \<^bold>.
\<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+
\<^bold>.
\<^bold>.
\<^bold>+ \<^bold>+ \<^bold>+ \<^bold>.
\<^bold>< \<^bold>+ \<^bold>+ \<^bold>.
\<^bold>> \<^bold>> \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>+ \<^bold>.
\<^bold>< \<^bold>.
\<^bold>+ \<^bold>+ \<^bold>+ \<^bold>.
\<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>. \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>- \<^bold>.
\<^bold>< \<^bold>+ \<^bold>. \<^bold>< 
\<box>"

definition hello_world_ascii :: "byte list" where
  "hello_world_ascii \<equiv> [72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33]"

  find_theorems compute_bf
  values "{zs. eval_bf bf_hello_world (initial_state []) zs}"
    
value "Predicate.the (compute_bf bf_hello_world (initial_state []))" (* 50 secs *)
export_code compute_bf Predicate.the checking Haskell

lemma hello_world: "eval_bf bf_hello_world 
    (initial_state [])
    (Normal (Tape [33, 100, 87, 0] 10 []) (Inp []) (Outp (rev hello_world_ascii)))"
  apply(simp add: hello_world_ascii_def bf_hello_world_def)
  apply auto
  apply(rule whileTrue, (simp; fail), auto)+
done

end
