{-# OPTIONS --rewriting #-}

module Main where

-- ============================================================
-- Maximally Multi-Focused Proofs for Skew Non-Commutative MILL
-- ============================================================

-- Some basic facts about lists
import Utilities

-- Formulae
import Formulae

-- Sequent calculus
import SeqCalc

-- Multi-focused sequent calculus
import MultifocSeqCalc

-- Maximally multi-focused sequent calculus
import MaxMultifocSeqCalc

-- ===========================================

-- Correctness of multi-focusing
-- -- Equational completeness
import correct.multifocus.EqComplete

-- -- Equational soundness
import correct.multifocus.EqSound

-- -- The sequent calculi are equivalent
import correct.multifocus.Iso1
import correct.multifocus.Iso2

-- ===========================================

import correct.max-multifocus.Lemmata

-- Correctness of max. multi-focusing
-- -- Equational completeness
-- import correct.max-multifocus.EqComplete

-- -- The sequent calculi are equivalent
import correct.max-multifocus.Iso1
import correct.max-multifocus.Iso2
