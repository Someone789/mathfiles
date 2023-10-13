(*  <<sympat.m;
    for Mathematica in kernel mode with a wide screen
    generate symmetric node patterns for the ndim-simplex in ndim>=1 dimensions up to a degree pmax>=0; ndim and pmax should not be large
    author: W.A. Mulder
    Spring 2022
*)
(*_______________________________________________________________________________________________________________________________*)
Clear["Global`*"];
(*_______________________________________________________________________________________________________________________________*)
(* user input *)
ndim = InputString["Number of space dimensions: ndim="];
If[StringLength[ndim]<1, ndim = 3,
   ndim = ToExpression[ndim] ];
If[ndim<1 || !IntegerQ[ndim], Print["Error: ndim should be an integer > 0"]; Return[]];

pmax = InputString["Maximum degree: pmax="];
If[StringLength[pmax]<1, pmax = 23; If[ndim>6, pmax=12], 
   pmax = ToExpression[pmax]];
If[pmax<0 || !IntegerQ[pmax], Print["Error: pmax should be an integer >= 0"]; Return[]];

useW = True; usew = InputString["Consider W as well (slower)?  [y(es)/n(o)]: "];
If[StringLength[usew]>0,
   usew = StringTake[usew,1]; useW = (usew=="y")|| (usew=="Y")|| (usew=="1")||(usew=="t")||(usew=="T");
];
(*_______________________________________________________________________________________________________________________________*)
SetOptions[$Output,PageWidth->145+27];  (* printing width *)
(*_______________________________________________________________________________________________________________________________*)
(* functions *)
Needs["Combinatorica`"];

Clear[NoSpaces];
NoSpaces::usage="NoSpaces[s] prints inputform of s as string without spaces";
NoSpaces[s_] := ToString[StringReplace[ToString[InputForm[s]], " " -> ""]]

Clear[MatrixTeXPrint];
MatrixTeXPrint::usage="MatrixTeXPrint[A,Asym,fileHandle]; prints matrix A in LaTeX format, or Asym=A is string Asym is defined";
MatrixTeXPrint[aa_,aasym_:"",fileHandle_:{}]:=Module[{na,b,i1,fp}, 
  na = Dimensions[aa];
  If[fileHandle=!={}, fp = fileHandle, fp = $Output];
  If[StringLength[aasym]>0, WriteString[fp,aasym<>"="]];
  WriteString[fp,"\\begin{pmatrix}\n"];
  Do[ b=aa[[i1]]//NoSpaces;
      WriteString[fp,StringReplace[b,{","->"&","{"->"","}"->""}]<>"\\\\\n"],
      {i1,na[[1]]}];
  WriteString[fp,"\\end{pmatrix}\n"];
];

Clear[CheckClass];
CheckClass::usage="{True/False,error}=CheckClass[nn] checks validity of input array nn; nn={2,1,1} in 3D, for instance; ndim=sum(nn)+1 in ndim dimensions";
CheckClass[nn_]:=Module[{err,na},
   If[!ArrayQ[nn], err = "class nn should be an array"; Return[{False,err}]];
   If[Length[Select[nn,#<0&]]>0, err = "class nn should not contain zeros"; Return[{False,err}]];
   (* non-increasing? *)
   na = Sort[nn]//Reverse;
   If[Max[Abs[na-nn]]=!=0, err = "array for class nn should have non-increasing entries"; Return[{False,err}]];
   {True,""}
];

Clear[NodeIndicesForClassBary]; 
NodeIndicesForClassBary::usage="jnodes=NodeIndicesForClassBary[nn] gives an integer representation of a generating node in sum(nn)-1 space dimensions for an equivalene class nn in the interior of the simplex. Map[a,jnodes,{2,2}] will produce a representation in terms of a[1], a[2], ... .";

NodeIndicesForClassBary[nn_]:=Module[{err,ndim1,x0,k,i0,i1},
  err = CheckClass[nn]; If[!err[[1]], Print["Error in NodeIndicesForClassBary: nn=",nn,", err_2=",err[[2]]]; Return[{}]];
  ndim1 = Plus@@nn; If[ nn[[1]]==ndim1, Return[ Array[1&,ndim1] ] ];
  x0 = Array[0&,ndim1]; i0=0; 
  Do[i1=i0+nn[[k]];
     x0[[ i0+1;;i1 ]] = k; (* refers to a[k] *)
     i0=i1, {k,Length[nn]}];
  x0
];

(*==============================================================================================================================*)
timingStart = AbsoluteTime[];
Print["========================================================================================================================================"];

(*_______________________________________________________________________________________________________________________________*)
(* xx = Table[x[k],{k,0,ndim}]; *)
nnclass = IntegerPartitions[ndim+1]; nclass = Length@nnclass; (* classes *)
Print["ndim=",ndim,"; pmax=",pmax,"; nclass=",nclass];

(* permutations *)
PermAll = Permutations[ Range[ndim+1] ]; 
PermClass = PermInvariants = Array[{}&,nclass];
Do[ jnode = NodeIndicesForClassBary[nnclass[[jclass]] ];
    jperms2 = Permute[jnode,PermAll];
    jperms1 = Union[jperms2];     
    ijperms = Table[ Flatten@Position[jperms2,jperms1[[j]]], {j,Length[jperms1]}];
    PermClass[[jclass]] = PermAll[[ ijperms[[All,1]] ]]; (* permutations for nodes of one class *)
    ijperms1 = ijperms[[1]]; 
    PermInvariants[[jclass]] = Table[ PermAll[[ ijperms1[[k]] ]],{k,Length[ijperms1]}]; (* node left invariant *)
    Null,{jclass,nclass}
];


(* Kreg is node pattern K for regular simplex *)
Kreg = Array[{},pmax+1]; 
For[pdeg=0,pdeg<=pmax,pdeg++,
  xpgen = IntegerPartitions[pdeg,ndim+1]; 
  xpgen = PadRight[xpgen,{Length[xpgen],ndim+1}]; (* padd with 0 to ndim+1 columns; *)
  (* generating nodes: xgen=(1+Reverse@xpgen)/(pdeg+ndim+1); *)
  xpclasses = Map[Reverse, Map[Sort, Map[Tally, xpgen][[All,All,2]] ] ]; (* ReverseSort not in older version *)
  Kreg[[pdeg+1]] = Count[xpclasses,#]& /@ nnclass;
];
(*_______________________________________________________________________________________________________________________________*)
(* matrix V *)
Print["V ..."];

gennodes = Table[NodeIndicesForClassBary[ nnclass[[j]] ],{j,nclass}];
VV = Array[0&,nclass,nclass];
If[useW, WW = VV; z2 = XPone = XPall = Array[{}&,nclass] ];
For[jclass=1,jclass<=nclass,jclass++,
  Print["ndim=",ndim,", class=",jclass,", nn=",NoSpaces[nnclass[[jclass]]]];
  vvrow = Array[0&,nclass]; xpall = Array[{}&,nclass]; If[useW, xpone = xpall];
  For[kc=1,kc<=nclass,kc++,
      xpkc = Permute[ gennodes[[kc]], PermClass[[kc]] ]; (* all nodes from a generating node of class kc *)          
      (* find invariant nodes from all classes, for the permutation subset defining the symmetry of gennodes[[kc]] *)
      For[j=1,j<=Length[xpkc],j++,
          xpu = Union[ Permute[ xpkc[[j]], PermInvariants[[jclass]] ] ]; (* inside if length 1 *)
          If[useW, xpall[[kc]] = Union@Append[xpall[[kc]],xpu] ];
          If[Length[xpu]==1,
             vvrow[[kc]]++; (* count in V if invariant, i.e., if length is 1 *)
             If[useW, xpone[[kc]] = Union@Append[xpone[[kc]],xpu] ];
          ];
      ];
  ];
  If[useW, 
    XPone[[jclass]] = xpone; XPall[[jclass]] = xpall;
    If[vvrow!=Length/@xpone, Print["inconsistency for xpone"]];
    WW[[jclass]] = Length/@xpall; (* lengths of elements in xpall *)
  ];
  VV[[jclass]] = vvrow;
  WriteString[$Output,"  V_",jclass,"=",NoSpaces[vvrow],"\n"];
];

Print[""]; WriteString[$Output,"V",ndim,"=",NoSpaces[VV],";"];
If[useW, Print[""]; WriteString[$Output,"W",ndim,"=",NoSpaces[WW],";"] ];
Print[""]; Print[""];
(*_______________________________________________________________________________________________________________________________*)
(* rhs ff *)
WriteString[$Output,"ff ... "];

ff = Array[0&,{nclass,pmax+1}]; If[useW, rr = ff];
Do[ (* monomial powers: pdeg*XBarySimplex[pdeg,ndim], Length[xpall]==Binomial[pdeg+ndim,pdeg] *)
    xpall = Compositions[pdeg,ndim+1];
    Do[ ti = Union@Table[ Union@Permute[ xpall[[j]], PermInvariants[[jclass]] ], {j,Length[xpall]}];
        ff[[jclass,pdeg+1]] = Count[Length/@ti,1]; (* invariant elements have length 1 *)
        If[useW, rr[[jclass,pdeg+1]] = Length[ti] ];
        Null,{jclass,nclass}
    ];
    If[ndim>2,WriteString[$Output," ",ToString[pdeg]]],
    {pdeg,0,pmax}
];
Print[""];

If[useW, (* IntegerPartitions[n, k] gives partitions of n into at most k integers *)
  rr1 = Table[Length@ IntegerPartitions[j,ndim+1],{j,0,pmax}];
  If[ Union[rr[[1]]-rr1]=={0}, Print["  rr_1 = Length@IntegerPartitions[p,ndim+1], p=0,...,pmax"]];
];
(*_______________________________________________________________________________________________________________________________*)
(* print rhs stored in ff *)
If[useW, Print[""]; WriteString[$Output,"rr",ndim,"="<>NoSpaces[rr],";"]; Print[""] ];
Print[""]; WriteString[$Output,"ff",ndim,"="<>NoSpaces[ff],";"]; Print[""];
Print[""];

(* check some rows of ff *)
bone = Table[ If[Mod[j,ndim+1]==0,1,0],{j,0,pmax}];
If[ Union[bone-ff[[1]]]==={0}, 
    Print["  ff_1 is 1 if Mod[p,ndim+1]==0 for degree p and zero otherwise"]];
btwo = Table[ 1+Floor[j/ndim],{j,0,pmax}];
If[ Union[btwo-ff[[2]]]==={0}, 
    Print["  ff_2 is 1+Floor[p/ndim] for degree p"]];

Clear[ndimg]; 
If[ndim>2,
   gfinvmin2 = (1+x)^2(1-x)^(ndimg-1);
   bmin1 = CoefficientList[ Series[(1/gfinvmin2)/.ndimg->ndim,{x,0,pmax}],x];
   bmin1 = PadRight[bmin1,Length[ff[[-3]]]];
   If[ Union[bmin1-ff[[-3]]]==={0}, 
      Print["  ff_",Length[ff]-2," (last-2) has generating function  1/( ",NoSpaces[gfinvmin2]," ) with ndimg=",ndim]; ]
];

gfinvmin1 = (1+x)(1-x)^ndimg;
bmin1 = CoefficientList[ Series[(1/gfinvmin1)/.ndimg->ndim,{x,0,pmax}],x];
bmin1 = PadRight[bmin1,Length[ff[[-2]]]];
If[ Union[bmin1-ff[[-2]]]==={0}, 
    Print["  ff_",Length[ff]-1," (last-1) has generating function  1/( ",NoSpaces[gfinvmin1]," ) with ndimg=",ndim]; ]

blast = Table[Binomial[j+ndim,ndim],{j,0,pmax}];
If[ Union[blast-ff[[-1]]]==={0}, 
    Print["  ff_",Length[ff]," (last) is Table[Binomial[j+ndim,ndim],{j,0,pmax}]"] ];
(*_______________________________________________________________________________________________________________________________*)
gf = 1/Table[FindGeneratingFunction[ff[[k]],x],{k,Length[ff]}]//Factor;
gf = Factor[gf/.(x-1)->-x1]/.x1->(1-x);
Print["  Generating functions for ff: 1/gf with gf=",NoSpaces[gf]];
(*_______________________________________________________________________________________________________________________________*)
(* node patterns kk from V^{-1} f *)
kkt = Inverse[VV].ff;
kk = Transpose[kkt]; pK = Table[ {j-1,kk[[j]]},{j,Length[kk]}];
WriteString[$Output,"\n{p,K}=",NoSpaces[pK],"\n"];
WriteString[$Output,"\nK^T=",NoSpaces[kkt],"\n"]; 

k1k2 = kk[[All,1]]+kk[[All,2]]; (*K1+K2*)
  k1k2a = Table[1+Floor[p/ndim],{p,0,Length[pK]-1}];
  If[Union[k1k2-k1k2a]=={0}, Print["  Checked: K1+K2=Floor[p/(ndim  )]+1 for ndim=",ndim] ];

  k1k2b = Table[1+Floor[p/(ndim+1)],{p,0,Length[pK]-1}];
  If[Union[k1k2-k1k2b]=={0}, Print["  Checked: K1+K2=Floor[p/(ndim+1)]+1 for ndim=",ndim] ];
(*_______________________________________________________________________________________________________________________________*)
Print["\n  Check against regular element ..."];
WriteString[$Output,"Kreg="<>NoSpaces[Kreg],"\n"];
Print[""];
Print["  Checking V.Kreg==ff for regular element ..."];
chkV = VV.Transpose[Kreg]-ff;
If[Union@Flatten@(chkV)==={0},
   Print["  V.Kreg==ff is OK for ndim=",ndim,", pmax=",pmax],
   Print["  V.Kreg==ff is WRONG for ndim=",ndim,", pmax=",pmax,"; see chV"]
];
If[UseW,
   Print["  Checking W.Kreg==rr for regular element ..."];
   chkW = WW.Transpose[Kreg]-rr;
   If[Union@Flatten@(chkW)==={0},
      Print["  W.Kreg==rr is OK for ndim=",ndim,", pmax=",pmax],
      Print["  W.Kreg==rr is WRONG for ndim=",ndim,", pmax=",pmax,"; see chkW"]];
];
Print[""];
(*_______________________________________________________________________________________________________________________________*)
(* LaTeX files *)

(* matrix V *)
Fname= "sympatv"<>ToString[ndim]<>".tex";
Fw = OpenWrite[Fname];
WriteString[Fw,"% ",Fname,"; ndim=",ndim,"\n"];
WriteString[Fw,"\\noindent $d="<>ToString[ndim]<>"$:{\\tiny{\n"];
WriteString[Fw,"\\["]; MatrixTeXPrint[VV   ,"\\mathbf{V}",Fw]; WriteString[Fw,",\\]\n"];
Close[Fw]; Print["See LaTeX fragment in ",Fname];

(* table with ff^T and K *)
fft = Transpose[ff]; nft = Dimensions[fft];
nkk = Dimensions[kk]; ncol = nkk[[2]];
Fname= "sympatk"<>ToString[ndim]<>".tex";
Fw = OpenWrite[Fname];(* Fw=$Output;*)
WriteString[Fw,"% \\newcommand{\\bfV}{\\mathbf{V}} \\newcommand{\\bfK}{\\mathbf{K}}\n"];
WriteString[Fw,"% \\newcommand{\\bff}{\\mathbf{f}} \\newcommand{\\pint}{p} \\newcommand{\\trp}{{\\mathsf{T}}}\n"];
WriteString[Fw,"\\begin{table}[ht]\n\\begin{center}\n"];
If[ndim==1,
   WriteString[Fw,"\\caption{Interior degree $\\pint$, the corresponding columns of $\\bff$ and the rows of $\\bfV^{-1}\\bff$, representing the node patterns $\\bfK$, in "<>ToString[ndim]<>" dimension.}\n"],
(*else*)
   WriteString[Fw,"\\caption{As Table~\\ref{tab:f1}, but in "<>ToString[ndim]<>" dimensions.}\n"]
]
WriteString[Fw,"\\label{tab:f",ndim,"}\n"];
WriteString[Fw,"\\begin{tabular}{r|"];
Do[ WriteString[Fw," r"],{k,ncol}]; WriteString[Fw,"|"];
Do[ WriteString[Fw," r"],{k,ncol}]; WriteString[Fw,"}\n"];
WriteString[Fw,"$\\pint$&\\multicolumn{"<>
      ToString[ncol]<>"}{c|}{$\\bff^\\trp$}&\\multicolumn{"<>
      ToString[ncol]<>"}{c}{$\\bfK$}\\\\ \\hline\n"];
Do[ WriteString[Fw, ToString[j-1]<>"&  " ]; (* degree *)
    Do[WriteString[Fw,ToString[fft[[j,k]]]<>"&"],{k,ncol}];WriteString[Fw,"  "];
    Do[WriteString[Fw,ToString[kk[[j,k]]]<>"&"],{k,ncol-1}];
    WriteString[Fw,ToString[kk[[j,-1]]]<>"\\\\ \n"],
    {j,nft[[1]]}];
WriteString[Fw,"\\end{tabular}\n"];
WriteString[Fw,"\\end{center}\\end{table}\n"];
Close[Fw]; Print["See LaTeX fragment in ",Fname];
(*_______________________________________________________________________________________________________________________________*)
Print["Used at most ",MaxMemoryUsed[]/2.^30," GBytes, so far; ",(AbsoluteTime[]-timingStart)/60.," minutes for ndim=",ndim];

(*EOF*)
