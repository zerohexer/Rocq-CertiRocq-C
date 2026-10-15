#!/usr/bin/env python3
"""kq_patch.py BUILD_DIR : three small changes to CertiRocq at commit 1b45a1aa.

 P1  theories/LambdaANF/toplevel.v -- the inliner's budget.  `inline_exp d j` halves j at every call it inlines, so the
     shipped 100 allows about six inlines along a path.  Calling a function of nine parameters needs eight (one per
     parameter, through the wrappers that uncurrying leaves), so in the shipped compiler such calls keep their wrappers:
     a heap closure per parameter per call.  Two changes: the budget becomes 100000, and `split_fuel` gives the
     inlined body a sixteenth of it instead of half (what follows the call keeps the rest).  The one lemma about
     `split_fuel` (its two parts add up to the whole) is re-proved; the pass and its proof are otherwise untouched.

 P3  theories/LambdaANF/toplevel.v -- what counts as a "small" function.  The two inline / shrink loops write out a
     function at its calls when its body is smaller than 10 (and has no `case` and does not call itself).  The wrapper
     that uncurrying leaves for parameter k+1 of a function has, once closures are made explicit, a body of size k + 3:
     it takes its k earlier arguments out of a record and builds the next closure.  So for a RECURSIVE function called
     from two or more places (called from one place, another rule removes the wrappers), the wrappers of the first seven
     parameters went and those of the eighth onward stayed: two heap objects and a call through a pointer per call,
     and -- because a closure's parameters can be anything -- saves around every call of that function.  The bound is
     now 40 (parameters up to the 37th).  It is a parameter of a proved pass; nothing else changes.

 P2  the plugin -- `CertiRocq Extract Inline [ c1, c2, .. ]`, backported from upstream commit 2dd374ee: the listed
     constants are handed to MetaRocq's inlining pass (which exists in this MetaRocq; the plugin passed the empty set)."""
import sys, os
B = sys.argv[1]
def rep(path, a, b, n=1):
    p = os.path.join(B, path); s = open(p).read()
    assert s.count(a) == n, (path, a[:70], s.count(a))
    open(p, 'w').write(s.replace(a, b)); print('patched', path, 'x%d' % n)

# ---- P1
rep('theories/LambdaANF/inline.v', '''  Definition split_fuel d : nat * nat :=
    let d2 := Nat.div2 d in
    (d2, d2 + Nat.b2n (Nat.odd d)).
''', '''  (* KQ patch (2026-10-13), see kq_patch.py: the body of an inlined call gets a sixteenth of the budget and what
     follows the call keeps the rest (it was: half each, so six inlines in a row used up a budget of 100) *)
  Lemma kq_div2_le : forall n, Nat.div2 n <= n.
  Proof. fix kq_rec 1. intros [| [| n]]; simpl; [ lia | lia | specialize (kq_rec n); lia ]. Qed.

  Definition split_fuel d : nat * nat :=
    let a := Nat.div2 (Nat.div2 (Nat.div2 (Nat.div2 d))) in
    (a, d - a).
''')
rep('theories/LambdaANF/inline.v', '''    unfold split_fuel. simpl. rewrite (Nat.div2_odd d) at 1. simpl.
    lia.
''', '''    unfold split_fuel. cbv zeta. simpl fst. simpl snd.
    pose proof (kq_div2_le d). pose proof (kq_div2_le (Nat.div2 d)).
    pose proof (kq_div2_le (Nat.div2 (Nat.div2 d))). pose proof (kq_div2_le (Nat.div2 (Nat.div2 (Nat.div2 d)))).
    lia.
''')
rep('theories/LambdaANF/toplevel.v', '  Section Pipeline.\n',
    '''  (* KQ patch (2026-10-13): the inliner's budget, see kq_patch.py.  100000, written as a product because the
     extracted compiler keeps a nat as a chain of cells and a literal of that size would be a term 100000 deep *)
  Definition kq_inline_fuel : nat := Nat.mul 400%nat 250%nat.
  Global Opaque kq_inline_fuel.
  (* KQ patch (2026-10-14): the size below which the inline / shrink loops write a function out at its calls (was 10) *)
  Definition kq_small_bound : nat := 40%nat.

  Section Pipeline.
''')
rep('theories/LambdaANF/toplevel.v', '(inline_uncurry next_var 10 100)', '(inline_uncurry next_var 10 kq_inline_fuel)')
rep('theories/LambdaANF/toplevel.v', '(inline_shrink_loop next_var 10 100)', '(inline_shrink_loop next_var kq_small_bound kq_inline_fuel)', 2)
rep('theories/LambdaANF/toplevel.v', '(inline_lifted next_var 10 1000)', '(inline_lifted next_var 10 kq_inline_fuel)')

# ---- P2
rep('plugins/common/certirocq_commands.mlg', '''VERNAC ARGUMENT EXTEND glueargs
''', '''VERNAC ARGUMENT EXTEND extract_inline
| [ reference(gr) ] -> { (constant_of_qualid ~loc gr) }
END

VERNAC ARGUMENT EXTEND glueargs
''')
rep('plugins/common/certirocq_commands.mlg', '''    Certirocq.register_constant_inductives inds
}
END
''', '''    Certirocq.register_constant_inductives inds
}
| [ "CertiRocq" "Extract" "Inline" "[" extract_inline_list_sep(csts, ",") "]" ] -> {
    Certirocq.register_inlines csts
}
END
''')
for pl in ('plugin', 'cplugin'):
    rep('plugins/%s/certirocq.ml' % pl, '''(* Extract Inductive to Constants *)
''', '''(* Extract Inline (KQ patch, after upstream 2dd374ee) *)

let global_inlining_registers =
  Summary.ref ~name:"CertiRocq Extraction Inlining Registration" Kernames.KernameSet.empty

let global_inlining_registers_name = "certirocq-inlining-registration"

let cache_inlining_registers (csts : Kernames.kername list) =
  global_inlining_registers :=
    List.fold_left (fun s k -> Kernames.KernameSet.add k s) !global_inlining_registers csts

let global_inlining_registers_input =
  let open Libobject in
  declare_object
    (global_object_nodischarge global_inlining_registers_name
    ~cache:(fun r -> cache_inlining_registers r)
    ~subst:None)

let register_inlines (csts : Kernames.kername list) : unit =
  Lib.add_leaf (global_inlining_registers_input csts)

let get_global_inlinings_mapping () = !global_inlining_registers

(* Extract Inductive to Constants *)
''')
    rep('plugins/%s/certirocq.ml' % pl, 'inlined_constants = Kernames.KernameSet.empty;', 'inlined_constants = get_global_inlinings_mapping ();')
    rep('plugins/%s/certirocq.mli' % pl, 'val register_constant_inductives : extract_inductives -> unit\n',
        'val register_constant_inductives : extract_inductives -> unit\nval register_inlines : Kernames.kername list -> unit\n')
