------------------------------------------------------------------------
-- Index of the formalisation of
--   L. Cohen, A. Grunfeld, "Multicategorical Semantics for Untyped
--   Effects" (submitted to MFPS 2026).
-- See README.md for the paper → module map and REPORT.md for the list
-- of issues found in the paper.
------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}
module MFPS.Everything where

import MFPS.Prelude          -- §2.1 renamings; arity casts
import MFPS.PROP             -- §2.3 pre-PROPs, PROPs, cartesian and Freyd PROPs
import MFPS.Preoperad        -- §3.1–3.2, §4.1 preoperads … weakly closed Freyd operads
import MFPS.Sub              -- §3.3 words, Fig. 3 congruence, ⋆ (Def. 3.15)
import MFPS.SubSound         -- Thm. 3.16
import MFPS.Representable    -- Cor. 3.17, Thm. 3.18 (i),(ii)
import MFPS.SubCast          -- arity casts as renaming steps
import MFPS.SubWhisker       -- Prop. 3.14 (i): the congruence is stable under whiskering
import MFPS.SubStrict        -- Prop. 3.14 (i): strictness laws of the premonoidal structure
import MFPS.SubCentral       -- Prop. 3.14 (i),(ii): centrality of steps and words
import MFPS.SubSym           -- Prop. 3.14 (i): the symmetry and its naturality
import MFPS.SubPROP          -- Prop. 3.14 (i): Sub_ℂ is a pre-PROP
import MFPS.SubCartesian     -- Prop. 3.14 (ii): Sub×_𝕍 is a cartesian PROP
import MFPS.SubFunctor       -- Prop. 3.14 (iv): functoriality in the preoperad
import MFPS.FreydSub         -- Def. 3.13, Prop. 3.14 (iii), Thm. 3.18 (iii)
import MFPS.FreydSubFunctor  -- Prop. 3.14 (iv): the induced Freyd PROP functor
import MFPS.PROPHet          -- pre-PROP computations up to arity casts; the identities behind Lemma A.1/A.7
import MFPS.PROPOperad       -- Def. 3.19 / Lemma A.1: the forgetful functor U
import MFPS.Uncurry          -- Def. A.5, Lemma A.6, Lemma A.7: interpreting words in a pre-PROP
import MFPS.FunctorOps       -- the categories FreydOp and FreydPROP
import MFPS.FreydAdjunction  -- Lemma A.2, A.4, A.8–A.10, Thm. 3.21 (F ⊣ U)
import MFPS.Syntax           -- §2.2 syntax, renaming, substitution
import MFPS.Theory           -- Fig. 2 equational theory, closure under ren/sub
import MFPS.Semantics        -- §4.1–4.2 structures, interpretation, soundness
import MFPS.TermModel        -- §4.3 term model: operations, unit laws, renaming actions
import MFPS.TermLaws         -- §4.3 Thm. 4.8: all laws of the term model
import MFPS.SubTuple         -- §4.2 tupling words: `plug` as a word of Sub_ℂ
import MFPS.SubstLemma       -- Lemma 4.5 (a),(b) for every structure; Thm. 4.7 (soundness), all cases
import MFPS.Completeness     -- §4.3 interpretation in the term model; Cor. 4.10 (completeness)
import MFPS.Initiality       -- §4.3 Thm. 4.9 (initiality of the term model)
import MFPS.CatSemantics     -- App. A.4: Def. A.12, A.14, Lemma A.15, Cor. A.13/A.16, completeness for Freyd PROPs
