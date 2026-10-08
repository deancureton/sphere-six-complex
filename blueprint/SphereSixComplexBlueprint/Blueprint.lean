import Verso
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoManual
import SphereSixComplexBlueprint.Chapters.Introduction
import SphereSixComplexBlueprint.Chapters.AnalyticConstruction
import SphereSixComplexBlueprint.Chapters.CuspGeometry
import SphereSixComplexBlueprint.Chapters.Topology
import SphereSixComplexBlueprint.Chapters.ReadingTheFormalization
import SphereSixComplexBlueprint.Chapters.Construction

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "A Complex Structure on the Six-Sphere" =>

A mathematical companion to the Lean formalization. Begin with the theorem and proof roadmap,
then follow the analytic family, cusp geometry, and global topology. The declaration reference
and dependency graph connect the explanations to the checked development.

{include 0 SphereSixComplexBlueprint.Chapters.Introduction}
{include 0 SphereSixComplexBlueprint.Chapters.AnalyticConstruction}
{include 0 SphereSixComplexBlueprint.Chapters.CuspGeometry}
{include 0 SphereSixComplexBlueprint.Chapters.Topology}
{include 0 SphereSixComplexBlueprint.Chapters.ReadingTheFormalization}
{include 0 SphereSixComplexBlueprint.Chapters.Construction}

{blueprint_graph}
{blueprint_summary}
