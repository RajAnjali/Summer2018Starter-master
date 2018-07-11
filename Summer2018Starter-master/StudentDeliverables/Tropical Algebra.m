(* ::Package:: *)

BeginPackage["TropicalAlgebra`"]

SetAttributes[TropicalPlus,Flat]
TropicalPlus[x_List, y_List] := MapThread[Min,{x,y}, Length[Dimensions[x]]]/;Dimensions[x]== Dimensions[y]
TropicalPlus[x_,y_]:=Min[x,y] 
Verbatim[TropicalPlus][x_]:=x

SetAttributes[TropicalTimes,Flat]
SetAttributes[TropicalMatrixTimes,Flat]
TropicalTimes[x_,y_]:=x+y
Verbatim[TropicalTimes][x_]:=x
TropicalMatrixTimes[a_List,b_List]:=Inner[Plus,a,b,Min]
Verbatim[TropicalMatrixTimes][x_List]:=x
TropicalMatrixSquare[a_List]:=Inner[Plus,a,a,Min]
TropicalMatrixTimes[a_,b_List]:=a+b

TropicalIdentityMatrix[n_Integer]:=IdentityMatrix[n]/.{1->0,0->Infinity}

TropicalTranspose[a_List] := Transpose[a]

TropicalConstantMatrixQ[a_List] := If[First[Counts[Flatten[a]]] == Length[Flatten[a]], True, False]

TropicalDeterminant[a_List]:= With[{n = First[Dimensions[a]]}, 
Min[Total[Table[Extract[a, Thread[{Range[n], perm}]], {perm, Permutations[Range[n]]}], {2}]]]/;SquareMatrixQ[a] == True

TropicalSingularQ[a_List]  := With[{terms=Table[Extract[a, Thread[{Range[First[Dimensions[a]]], perm}]], {perm, Permutations[Range[First[Dimensions[a]]]]}]}, 
If[First[Counts[Sort[Total[terms, {2}]]]] > 1 , True, False]]/;SquareMatrixQ[a] == True

TropicalRank[a_List] :=
(
r = First[Dimensions[a]];
minor= Table[Flatten[Minors[a,i,Identity],1], {i, r}];
While[AllTrue[minor[[r]],TropicalSingularQ], r--];
r
)/;SquareMatrixQ[a] == True

TropicalExp[a_, n_] := n a
TropicalMatrixExp[a_List,n_Integer]:= If[n==1, a+1]/; n<2
TropicalMatrixExp[a_List,n_Integer]:=Nest[TropicalMatrixSquare,a,n/2]/;EvenQ[n]
TropicalMatrixExp[a_List,n_Integer]:=TropicalMatrixTimes[Nest[TropicalMatrixSquare, a, (n-1)/2], a]/;OddQ[n]

TropicalPolynomial[p_List, x_List] := ( n = First[Dimensions[x]];
temp = First[p]+TropicalIdentityMatrix[n];
For[i=0, i<Length[p], i++, 
temp = TropicalPlus[TropicalMatrixTimes[(temp), x], (p[[i+1]]+TropicalIdentityMatrix[n])];];
temp
)

f[a_,b_] := tropicalPlus[tropicalTimes[a, x],b]
TropicalPolynomial[p_List, x_] :=  Fold[ f, p]/.{tropicalPlus->Min,tropicalTimes->Plus}

TropicalPolynomialTimes[a_, b_, x_] := Expand[a*b]/. {Plus -> Min, Times -> Plus, x^n_->n*x}

TropicalAdjointMatrix[a_List] := With[{n = First[Dimensions[a]], m = Minors[a/.{Infinity -> w},First[Dimensions[a]]-1,Identity]}, 
Transpose[Partition[ TropicalDeterminant/@( Flatten[Reverse[Reverse[m, n-1]], 1]/. {w -> Infinity}), n]]]/;SquareMatrixQ[a] == True

TropicalMatrixInverse[a_List] := TropicalAdjointMatrix[a]-TropicalDeterminant[a]/;SquareMatrixQ[a] == True

GetEigenvalueData[a_List]:=Module[{isConstantMatrix,x,k,j,i,c,p,\[Lambda],listX={}},
isConstantMatrix=False; 
x[0] = TropicalIdentityMatrix[Length[a]][[All, 1]];
k= 0;
While[!isConstantMatrix,
(x[k+1]=TropicalMatrixTimes[a,x[k]];
For[j=0,j<=k,j++,
If[TropicalConstantMatrixQ[x[k+1]-x[j]],
isConstantMatrix=True;
c=x[k+1]-x[j];
p=k+1-j;]
];
k++;)
];
For[i=0,i<=k,i++,
listX=Append[listX,x[i]]
];
k=k-p;
\[Lambda] = N[c[[1]]/p];
{{c[[1]],p,k,\[Lambda]},listX}
]

TropicalEigenValue[a_List] :=GetEigenvalueData[a][[1,4]]

TropicalEigenVector[a_List] := Module[{eigenvalueData={},listX={},\[Lambda],p,k,t}, 
eigenvalueData=GetEigenvalueData[a];
\[Lambda]=eigenvalueData[[1,4]];
k=eigenvalueData[[1,3]];
p=eigenvalueData[[1,2]];
listX=eigenvalueData[[2]];
t=First[Transpose[TropicalIdentityMatrix[Length[a]]]]/. 0->Infinity;
For[j= 1, j<=p, j++, 
t = TropicalPlus[TropicalMatrixTimes[TropicalExp[\[Lambda], p-j], listX[[k+j-1]]], t];];
t
]

EndPackage[]
