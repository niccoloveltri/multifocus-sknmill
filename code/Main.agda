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

-- -- WIP

-- Correctness of multi-focusing
-- -- Equational completeness
import correct.multifocus.EqComplete
