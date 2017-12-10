/**CFile****************************************************************

  FileName    [lsv1SubFind.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [lsv: Logic Synthesis and Verification PA.]

  Synopsis    [procedure for finding 1-input resubstitution candidates.]

  Author      [Hao Chen]
  
  Affiliation [NTU]

  Date        [12, Dec., 2017.]

***********************************************************************/

#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"
#include "proof/fraig/fraig.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        ITERATORS                                 ///
////////////////////////////////////////////////////////////////////////
#define Abc_NtkForEachNodeStart(pNtk, pNode, i, start)                                        \
  for (i = start; i < Vec_PtrSize((pNtk)->vObjs) && ((pNode = Abc_NtkObj(pNtk, i)), 1); ++i)  \
    if (pNode == NULL || !Abc_ObjIsNode(pNode)) {} else

#define Abc_NtkForEachNodeStop(pNtk, pNode, i, stop)                                          \
  for (i = 0; i < stop && ((pNode = Abc_NtkObj(pNtk, i)), 1); ++i)                            \
    if (pNode == NULL || !Abc_ObjIsNode(pNode)) {} else

#define Abc_NtkForEachNodeStartStop(pNtk, pNode, i, start, stop)                              \
  for (i = start; i < stop && ((pNode = Abc_NtkObj(pNtk, i)), 1); ++i)                        \
    if (pNode == NULL || !Abc_ObjIsNode(pNode)) {} else

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
extern "C" Vec_Ptr_t* Abc_NtkPartitionSmart(Abc_Ntk_t* pNtk, int nPartSizeLimit, int fVerbose);
extern "C" void       Abc_NtkConvertCos(Abc_Ntk_t* pNtk, Vec_Int_t* vOuts, Vec_Ptr_t* vOnePtr);

// simulation
extern "C" void       Abc_NtkXValueSimulate(Abc_Ntk_t* pNtk, int nFrames, int fXInputs, int fXState, int fVerbose);
static inline int     Abc_XsimRand2() { return (rand() & 1) ? ABC_INIT_ONE : ABC_INIT_ZERO; }
static inline void    Abc_ObjSetXsim(Abc_Obj_t* pObj, int Value)  { pObj->pCopy = (Abc_Obj_t* )(ABC_PTRINT_T)Value;  }
static inline int     Abc_ObjGetXsim(Abc_Obj_t* pObj)             { return (int)(ABC_PTRINT_T)pObj->pCopy;           }
static inline int Abc_XsimInv(int Value) { 
  if (Value == ABC_INIT_ZERO) return ABC_INIT_ONE;
  else if (Value == ABC_INIT_ONE) return ABC_INIT_ZERO;
  assert(Value == ABC_INIT_DC);       
  return ABC_INIT_DC;
}
static inline int Abc_XsimAnd(int Value0, int Value1) { 
  if (Value0 == ABC_INIT_ZERO || Value1 == ABC_INIT_ZERO) return ABC_INIT_ZERO;
  if (Value0 == ABC_INIT_DC || Value1 == ABC_INIT_DC) return ABC_INIT_DC;
  assert(Value0 == ABC_INIT_ONE && Value1 == ABC_INIT_ONE);
  return ABC_INIT_ONE;
}
static inline int Abc_ObjGetXsimFanin0(Abc_Obj_t* pObj) { 
  int retValue = Abc_ObjGetXsim(Abc_ObjFanin0(pObj));
  return Abc_ObjFaninC0(pObj)? Abc_XsimInv(retValue) : retValue;
}
static inline int Abc_ObjGetXsimFanin1(Abc_Obj_t* pObj) { 
  int retValue = Abc_ObjGetXsim(Abc_ObjFanin1(pObj));
  return Abc_ObjFaninC1(pObj)? Abc_XsimInv(retValue) : retValue;
}


// lsv functions
void  Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk);
int   Lsv_SimCheck(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int pObj_fId, int pObj_gId, int nTimes);
int   Lsv_Is1Sub(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int pObj_fId, int pObj_gId); 
int   Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
int   Lsv_NtkCecFraigPartAuto(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
void  Lsv_Ntk1SubDump(Vec_Ptr_t* vTable, Abc_VerbLevel level);
void  Lsv_Ntk1SubDumpFile(Vec_Ptr_t* vTable, FILE* fp);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk) {
  assert(Abc_NtkIsTopo(pNtk));
  abctime clk = Abc_Clock();
  Abc_Obj_t* pObj_f = 0; // to be merged
  Abc_Obj_t* pObj_g = 0; // to merge someone

  int i = 0, j = 0, k = 0;
  Vec_Ptr_t* vTable = Vec_PtrStart(0);
  Abc_Ntk_t* pNtk_dup = Abc_NtkDup(pNtk);
  Vec_Int_t* vWhichFanin = Vec_IntStart(0);
  Abc_NtkForEachNode(pNtk, pObj_f, i) {
    Vec_Ptr_t* vNodes = Vec_PtrStart(0);
    Abc_NtkForEachNode(pNtk, pObj_g, j) {
      if (i == j) continue;
      // merge g to f
      Abc_Obj_t* pFanout = 0;
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        if (Abc_ObjFaninId0(pObj) == i) {
          pObj->vFanins.pArray[0] = j;
          Vec_IntPush(vWhichFanin, 0);
        }
        else {
          pObj->vFanins.pArray[1] = j;
          Vec_IntPush(vWhichFanin, 1);
        }
      }
      if (Abc_NtkIsAcyclic(pNtk_dup)) {
        Abc_Ntk_t* pNtk_dup_strash = Abc_NtkStrash(pNtk_dup, 0, 1, 0);
        // perform fast sim check
        if (Lsv_SimCheck(pNtk, pNtk_dup_strash, i, j, 10)) {
          // check 1sub
          if (Lsv_Is1Sub(pNtk, pNtk_dup_strash, i, j)) {
            Vec_PtrPush(vNodes, pObj_g);
          }
        }
        Abc_NtkDelete(pNtk_dup_strash);
      }
      // recover
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        pObj->vFanins.pArray[Vec_IntEntry(vWhichFanin, k)] = i;
      }
      Vec_IntClear(vWhichFanin);
    }
    Vec_PtrPush(vNodes, pObj_f);
    Vec_PtrPush(vTable, vNodes);
  }
  Vec_IntFree(vWhichFanin);
  Abc_NtkDelete(pNtk_dup);
  
  // print result
  Lsv_Ntk1SubDump(vTable, ABC_STANDARD);
  Vec_PtrFreeFree(vTable);
  Abc_PrintTime(ABC_STANDARD, "Time", Abc_Clock() - clk);
}

int Lsv_SimCheck(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int pObj_fId, int pObj_gId, int nTimes) {
  return 1;
  assert(Abc_NtkIsStrash(pNtk1) && Abc_NtkIsStrash(pNtk2));
  Abc_ObjSetXsim(Abc_AigConst1(pNtk1), ABC_INIT_ONE);
  Abc_ObjSetXsim(Abc_AigConst1(pNtk2), ABC_INIT_ONE);
  int i = 0;
  Abc_Obj_t* pObj = 0;
  int retValue = 1; 
  for (int t = 0; t < 64 * nTimes; ++t) {
    int simValue[Abc_NtkPiNum(pNtk1)];
    for (int j = 0; j < Abc_NtkPiNum(pNtk1); ++j) {
      simValue[j] = Abc_XsimRand2();
    }
    Abc_NtkForEachPi(pNtk1, pObj, i)  Abc_ObjSetXsim(pObj, simValue[i]);
    Abc_AigForEachAnd(pNtk1, pObj, i)  Abc_ObjSetXsim(pObj, Abc_XsimAnd(Abc_ObjGetXsimFanin0(pObj), Abc_ObjGetXsimFanin1(pObj)));
    Abc_NtkForEachPo(pNtk1, pObj, i)   Abc_ObjSetXsim(pObj, Abc_ObjGetXsimFanin0(pObj));
    
    Abc_NtkForEachPi(pNtk2, pObj, i)  Abc_ObjSetXsim(pObj, simValue[i]);
    Abc_AigForEachAnd(pNtk2, pObj, i) Abc_ObjSetXsim(pObj, Abc_XsimAnd(Abc_ObjGetXsimFanin0(pObj), Abc_ObjGetXsimFanin1(pObj)));
    Abc_NtkForEachPo(pNtk2, pObj, i)  Abc_ObjSetXsim(pObj, Abc_ObjGetXsimFanin0(pObj));
    
    // Abc_NtkForEachPo(pNtk1, pObj, i) printf(" %d", Abc_ObjGetXsim(Abc_NtkPo(pNtk1, i))); printf("\n");
    // Abc_NtkForEachPo(pNtk2, pObj, i) printf(" %d", Abc_ObjGetXsim(Abc_NtkPo(pNtk2, i))); printf("\n");
    for (int j = 0; j < Abc_NtkPoNum(pNtk1); ++j) {
      if (Abc_ObjGetXsim(Abc_NtkPo(pNtk1, j)) ^ Abc_ObjGetXsim(Abc_NtkPo(pNtk2, j))) {
        retValue = 0;
        break;
      }
    }
    if (!retValue) break;
  }
  if (retValue) {
    return 1;
  }
  // Abc_Ntk_t* pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 0, 0, 0);
  // Abc_NtkDelete(pMiter);
  Abc_Obj_t* pFanout = 0;
  Abc_ObjForEachFanout(Abc_NtkObj(pNtk1, pObj_fId), pFanout, i) {
    if (Abc_ObjId(pFanout) >= Abc_NtkObjNum(pNtk2)) continue;
    Abc_Obj_t* pTmp = Abc_NtkObj(pNtk2, Abc_ObjId(pFanout));
    if (pTmp == NULL) continue;
    if (Abc_ObjFaninId0(pFanout) == pObj_fId) Abc_ObjXorFaninC(pTmp, 0);
    else Abc_ObjXorFaninC(pTmp, 1);
  }
  for (int t = 0; t < nTimes; ++t) {
    int simValue[Abc_NtkPiNum(pNtk1)];
    for (int j = 0; j < Abc_NtkPiNum(pNtk1); ++j) {
      simValue[j] = Abc_XsimRand2();
    }
    Abc_NtkForEachPi(pNtk1, pObj, i)   Abc_ObjSetXsim(pObj, simValue[i]);
    Abc_AigForEachAnd(pNtk1, pObj, i)  Abc_ObjSetXsim(pObj, Abc_XsimAnd(Abc_ObjGetXsimFanin0(pObj), Abc_ObjGetXsimFanin1(pObj)));
    Abc_NtkForEachPo(pNtk1, pObj, i)   Abc_ObjSetXsim(pObj, Abc_ObjGetXsimFanin0(pObj));
    
    Abc_NtkForEachPi(pNtk2, pObj, i)  Abc_ObjSetXsim(pObj, simValue[i]);
    Abc_AigForEachAnd(pNtk2, pObj, i) Abc_ObjSetXsim(pObj, Abc_XsimAnd(Abc_ObjGetXsimFanin0(pObj), Abc_ObjGetXsimFanin1(pObj)));
    Abc_NtkForEachPo(pNtk2, pObj, i)  Abc_ObjSetXsim(pObj, Abc_ObjGetXsimFanin0(pObj));
    for (int j = 0; j < Abc_NtkPoNum(pNtk1); ++j) {
      if (Abc_ObjGetXsim(Abc_NtkPo(pNtk1, j)) ^ Abc_ObjGetXsim(Abc_NtkPo(pNtk2, j))) {
        return 0;
      }
    }
  }
  return 1; // 0: doesn't pass, 1: pass
}

int Lsv_Is1Sub(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int pObj_fId, int pObj_gId) {
  // pObj_g merges pObj_f
  assert(Abc_NtkIsStrash(pNtk2));
  int result = Lsv_NtkCecFraig(pNtk1, pNtk2);
  if (result) {
    return 1;
  }
  int i = 0; 
  Abc_Obj_t* pFanout = 0;
  Abc_ObjForEachFanout(Abc_NtkObj(pNtk1, pObj_fId), pFanout, i) {
    if (Abc_ObjId(pFanout) >= Abc_NtkObjNum(pNtk2)) continue;
    Abc_Obj_t* pTmp = Abc_NtkObj(pNtk2, Abc_ObjId(pFanout));
    if (pTmp == NULL) continue;
    if (Abc_ObjFaninId0(pFanout) == pObj_fId) Abc_ObjXorFaninC(pTmp, 0);
    else Abc_ObjXorFaninC(pTmp, 1);
  }
  return Lsv_NtkCecFraig(pNtk1, pNtk2);
}

int Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2) {
  // get the miter of the two networks
  Abc_Ntk_t* pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 0, 0, 0);
  if (pMiter == NULL) {
    Abc_Print(ABC_ERROR, "Miter computation has failed.\n");
    return 0;
  }
  // handle trivial case
  int retValue = Abc_NtkMiterIsConstant(pMiter);
  if (retValue == 0 || retValue == 1) {
    Abc_NtkDelete(pMiter);
    return retValue;
  }
  Abc_ObjSetXsim(Abc_AigConst1(pMiter), ABC_INIT_ONE);
  Abc_Obj_t* pObj = 0;
  int i = 0;
  for (int t = 0; t < 64 * 10; ++t) {
    int simValue[Abc_NtkPiNum(pMiter)];
    for (int j = 0; j < Abc_NtkPiNum(pMiter); ++j) {
      simValue[j] = Abc_XsimRand2();
    }
    Abc_NtkForEachPi(pMiter, pObj, i)   Abc_ObjSetXsim(pObj, simValue[i]);
    Abc_AigForEachAnd(pMiter, pObj, i)  Abc_ObjSetXsim(pObj, Abc_XsimAnd(Abc_ObjGetXsimFanin0(pObj), Abc_ObjGetXsimFanin1(pObj)));
    Abc_NtkForEachPo(pMiter, pObj, i)   Abc_ObjSetXsim(pObj, Abc_ObjGetXsimFanin0(pObj));
    if (Abc_ObjGetXsim(Abc_NtkPo(pMiter, 0)) != ABC_INIT_ZERO) {
      Abc_NtkDelete(pMiter);
      return 0;
    }
  }
  // solve the CNF using the SAT solver
  Prove_Params_t Params, *pParams = &Params;
  Prove_ParamsSetDefault(pParams);
  pParams->nItersMax = 5;
  retValue = Abc_NtkIvyProve(&pMiter, pParams);
  Abc_NtkDelete(pMiter);
  return retValue;
}

int Lsv_NtkCecFraigPartAuto(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2) {
  // get the miter of the two networks
  Abc_Ntk_t* pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 1, 0, 0);
  if (pMiter == NULL) {
    Abc_Print(ABC_ERROR, "Miter computation has failed.\n" );
    return 0;
  }
  int retValue = Abc_NtkMiterIsConstant(pMiter);
  if (retValue == 0 || retValue == 1) {
    Abc_NtkDelete(pMiter);
    return retValue;
  }
  // solve the CNF using the SAT solver
  Prove_Params_t Params, *pParams = &Params;
  Prove_ParamsSetDefault(pParams);
  pParams->nItersMax = 5;
  // partition the outputs
  Vec_Ptr_t* vParts = Abc_NtkPartitionSmart(pMiter, 300, 0);

  // fraig each partition
  int status = 1;
  int nOutputs = 0;
  int i = 0;
  Vec_Ptr_t* vOnePtr = Vec_PtrAlloc(1000);
  Vec_Int_t* vOne = 0;
  Vec_PtrForEachEntry(Vec_Int_t*, vParts, vOne, i) {
    // get this part of the miter
    Abc_NtkConvertCos(pMiter, vOne, vOnePtr);
    Abc_Ntk_t* pMiterPart = Abc_NtkCreateConeArray(pMiter, vOnePtr, 0);
    Abc_NtkCombinePos(pMiterPart, 0, 0);
    // check the miter for being constant
    retValue = Abc_NtkMiterIsConstant(pMiterPart);
    if (retValue == 0) {
      status = 0;
      Abc_NtkDelete(pMiterPart);
      break;
    }
    else if (retValue == 1) {
      Abc_NtkDelete(pMiterPart);
      continue;
    }
    // solve the problem
    retValue = Abc_NtkIvyProve(&pMiterPart, pParams);
    if (retValue == -1) {
      status = -1;
      Abc_NtkDelete(pMiterPart);
      break;
    }
    else if (retValue == 0) {
      status = 0;
      Abc_NtkDelete(pMiterPart);
      break;
    }
    else {
      nOutputs += Vec_IntSize(vOne);
    }
    Abc_NtkDelete(pMiterPart);
  }
  Vec_VecFree((Vec_Vec_t*)vParts);
  Vec_PtrFree(vOnePtr);
  Abc_NtkDelete(pMiter);
  if (status == 1) return 1;
  else return 0;
}

void  Lsv_Ntk1SubDump(Vec_Ptr_t* vTable, Abc_VerbLevel level) {
  Vec_Ptr_t* vNodes = 0;
  Abc_Obj_t* pEntry = 0;
  Abc_Print(level, "\n");
  int i = 0, j = 0;
  Vec_PtrForEachEntry(Vec_Ptr_t*, vTable, vNodes, i) {
    Abc_Print(level, "n%d:", Abc_ObjId((Abc_Obj_t*)Vec_PtrEntryLast(vNodes)));
    Vec_PtrForEachEntryStop(Abc_Obj_t*, vNodes, pEntry, j, Vec_PtrSize(vNodes) - 1) {
      Abc_Print(level, " n%d", Abc_ObjId(pEntry));
    }
    Abc_Print(level, "\n");
  }
  Abc_Print(level, "\n");
}

void  Lsv_Ntk1SubDumpFile(Vec_Ptr_t* vTable, FILE* fp, char* filename) {
  fp = fopen(filename, "w");
  Vec_Ptr_t* vNodes = 0;
  Abc_Obj_t* pEntry = 0;
  fprintf(fp, "\n");
  int i = 0, j = 0;
  Vec_PtrForEachEntry(Vec_Ptr_t*, vTable, vNodes, i) {
    fprintf(fp, "n%d:", Abc_ObjId((Abc_Obj_t*)Vec_PtrEntryLast(vNodes)));
    Vec_PtrForEachEntryStop(Abc_Obj_t*, vNodes, pEntry, j, Vec_PtrSize(vNodes) - 1) {
      fprintf(fp, " n%d", Abc_ObjId(pEntry));
    }
    fprintf(fp, "\n");
  }
  fprintf(fp, "\n");
}

ABC_NAMESPACE_IMPL_END