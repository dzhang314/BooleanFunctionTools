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

Unprotect["BooleanFunctionTools`*"];
ClearAll["BooleanFunctionTools`*"];
ClearAll["BooleanFunctionTools`Private`*"];

CertificateQ::usage = "TODO";
Certificates::usage = "TODO";
CertificateComplexity::usage = "TODO";

SensitiveBitQ::usage = "TODO";
SensitiveBits::usage = "TODO";
Sensitivity::usage = "TODO";

SensitiveBlockQ::usage = "TODO";
SensitiveBlocks::usage = "TODO";
MinimalSensitiveBlocks::usage = "TODO";
MaximalSensitiveBlockFamilies::usage = "TODO";
BlockSensitivity::usage = "TODO";

BinaryDecisionTrees::usage = "TODO";
EvaluateTree::usage = "TODO";
BooleanFunctionIndex::usage = "TODO";

Begin["`Private`"];

(* =================================================== CERTIFICATE COMPLEXITY *)

CertificateQ[f_, x_List, s_List] := AllTrue[
    Tuples[{0, 1}, Length[x]],
    Implies[x[[s]] === #[[s]], f @@ x === f @@ #]&
];

Certificates[f_, x_List] := Select[
    Subsets@Range@Length[x],
    CertificateQ[f, x, #]&
];

CertificateComplexity[f_, x_List] := Min[Length /@ Certificates[f, x]];

CertificateComplexity[f_, n_Integer] := Max[
    CertificateComplexity[f, #]& /@ Tuples[{0, 1}, n]
];

(* ============================================================== SENSITIVITY *)

FlipBit[x_List, i_Integer] := MapAt[1 - #&, x, i];

SensitiveBitQ[f_, x_List, i_Integer] := (f @@ x) =!= (f @@ FlipBit[x, i]);

SensitiveBits[f_, x_List] := Select[Range@Length[x], SensitiveBitQ[f, x, #]&];

Sensitivity[f_, x_List] := Length@SensitiveBits[f, x];

Sensitivity[f_, n_Integer] := Max[Sensitivity[f, #]& /@ Tuples[{0, 1}, n]];

(* ======================================================== BLOCK SENSITIVITY *)

FlipBlock[x_List, s_List] := MapAt[1 - #&, x, List /@ s];

SensitiveBlockQ[f_, x_List, s_List] := (f @@ x) =!= (f @@ FlipBlock[x, s]);

SensitiveBlocks[f_, x_List] := Select[
    Subsets@Range@Length[x],
    SensitiveBlockQ[f, x, #]&
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

BlockSensitivity[f_, x_List] :=
    Max[Length /@ DisjointSubsets@MinimalSensitiveBlocks[f, x]];

BlockSensitivity[f_, n_Integer] := Max@Map[
    BlockSensitivity[f, #]&,
    Tuples[{0, 1}, n]
];

(* ================================================= DECISION TREE COMPLEXITY *)

BinaryDecisionTrees[vars_List, 0] := {0, 1};

BinaryDecisionTrees[vars_List, depth_Integer] :=
BinaryDecisionTrees[vars, depth] = Union[
    Flatten@Table[
        {vars[[i]][a, b], vars[[i]][b, a]},
        {i, Length[vars]},
        {n, 0, depth - 2},
        {a, BinaryDecisionTrees[Delete[vars, i], depth - 1]},
        {b, BinaryDecisionTrees[Delete[vars, i], n]}
    ],
    Flatten@Table[
        If[a === b, Nothing, vars[[i]][a, b]],
        {i, Length[vars]},
        {a, BinaryDecisionTrees[Delete[vars, i], depth - 1]},
        {b, BinaryDecisionTrees[Delete[vars, i], depth - 1]}
    ]
];

EvaluateTree[0, _] = 0;

EvaluateTree[1, _] = 1;

EvaluateTree[i_[a_, b_], x_List] :=
    If[x[[i]] === 0, EvaluateTree[a, x], EvaluateTree[b, x]];

BooleanFunctionIndex[tree_, n_Integer] :=
    FromDigits[Reverse[EvaluateTree[tree, #]& /@ Tuples[{0, 1}, n]], 2];

(* ========================================================================== *)

End[]; (* `Private` *)
(* Protect["BooleanFunctionTools`*"]; *)
EndPackage[]; (* BooleanFunctionTools` *)
