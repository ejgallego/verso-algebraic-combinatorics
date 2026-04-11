import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import AlgebraicCombinatoricsBlueprint.TeXPrelude
import AlgebraicCombinatoricsBlueprint.Chapters.NotationsExamples
import AlgebraicCombinatoricsBlueprint.Chapters.CommutativeRings
import AlgebraicCombinatoricsBlueprint.Chapters.FPSDefinition
import AlgebraicCombinatoricsBlueprint.Chapters.DividingFPS
import AlgebraicCombinatoricsBlueprint.Chapters.Polynomials
import AlgebraicCombinatoricsBlueprint.Chapters.Substitution
import AlgebraicCombinatoricsBlueprint.Chapters.Derivatives
import AlgebraicCombinatoricsBlueprint.Chapters.ExpLog

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic Combinatorics Blueprint" =>

This repository is the Verso blueprint integration layer for the Algebraic
Combinatorics project. It keeps the blueprint files at the repository root
while treating `algebraic-combinatorics/` as the upstream formalization
checkout.

{include 0 AlgebraicCombinatoricsBlueprint.Chapters.NotationsExamples}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.CommutativeRings}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.FPSDefinition}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.DividingFPS}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.Polynomials}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.Substitution}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.Derivatives}
{include 0 AlgebraicCombinatoricsBlueprint.Chapters.ExpLog}

{blueprint_graph}
{blueprint_summary}
