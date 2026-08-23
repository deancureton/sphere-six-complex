import Verso
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoManual
import SphereSixComplexBlueprint.Chapters.Introduction
import SphereSixComplexBlueprint.Chapters.Construction

open Informal
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "A Complex Structure on the Six-Sphere" =>

This Blueprint tracks the formalization of the compact complex threefold constructed in the source
paper and the proof that its underlying smooth manifold is diffeomorphic to the six-sphere.

{include 0 SphereSixComplexBlueprint.Chapters.Introduction}
{include 0 SphereSixComplexBlueprint.Chapters.Construction}

{blueprint_graph}
{blueprint_summary}
