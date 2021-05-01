(* ::Package:: *)

(* :Title: BooleanFunctionTools *)
(* :Context: BooleanFunctionTools` *)
(* :Author: David K. Zhang *)
(* :Date: 2021-05-01 *)

(* :Package Version: 1.0 *)
(* :Wolfram Language Version: 12.1 *)

(* :Summary: BooleanFunctionTools is a Wolfram Language package for computing
             various theoretical complexity measures, such as decision tree
             complexity, certificate complexity, sensitivity, and degree of
             Boolean functions. *)

(* :Copyright: (c) 2021 David K. Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. *)

BeginPackage["BooleanFunctionTools`"];

SensitiveBlocks::usage = "TODO";
MinimalSensitiveBlocks::usage = "TODO";
MaximalSensitiveBlockFamilies::usage = "TODO";
BlockSensitivity::usage = "TODO";

Begin["`Private`"];

(* ======================================================== BLOCK SENSITIVITY *)

FlipBlock[x_List, s_List] := MapAt[1 - #&, x, List /@ s];

SensitiveBlocks[f_, x_List] := Select[
	Subsets@Range@Length[x],
	(f @@ x) =!= (f @@ FlipBlock[x, #])&
];

ProperSubsetQ[xs_List][ys_List] :=
	(Length[ys] < Length[xs]) && SubsetQ[xs, ys];

MinimalSensitiveBlocks[f_, x_List] := With[
	{blocks = SensitiveBlocks[f, x]},
	Select[blocks, NoneTrue[blocks, ProperSubsetQ[#]]&]
];

DisjointSubsets[{}] = {{}};
DisjointSubsets[xs_List] := With[
	{x = First[xs], r = Rest[xs]},
	Union[
		Prepend[x] /@ DisjointSubsets@Select[r, DisjointQ[x, #]&],
		DisjointSubsets[r]
	]
];

MaximalSensitiveBlockFamilies[f_, x_List] :=
	MaximalBy[DisjointSubsets@MinimalSensitiveBlocks[f, x], Length];

BlockSensitivity[f_, n_Integer] := Max@Map[
	Max[Length /@ DisjointSubsets@MinimalSensitiveBlocks[f, #]]&,
	Tuples[{0, 1}, n]
];

(* ========================================================================== *)

End[]; (* `Private` *)
EndPackage[]; (* BooleanFunctionTools` *)
