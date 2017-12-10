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

void  Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk);
int   Lsv_Is1Sub(Abc_Ntk_t* pNtk, int pObj_fId, int pObj_gId); 
int   Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
int   Lsv_NtkCecFraigPartAuto(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk) {
  assert(Abc_NtkIsTopo(pNtk));
  abctime clk = Abc_Clock();
  Abc_Obj_t* pObj_f = 0; // to be merged
  Abc_Obj_t* pObj_g = 0; // to merge someone

  int i = 0, j = 0;
  Vec_Ptr_t* vTable = Vec_PtrStart(0);
  Abc_NtkForEachNode(pNtk, pObj_f, i) {
    Vec_Ptr_t* vNodes = Vec_PtrStart(0);
    Abc_NtkForEachNode(pNtk, pObj_g, j) {
      if (i == j) continue;
      if (Lsv_Is1Sub(pNtk, Abc_ObjId(pObj_f), Abc_ObjId(pObj_g))) {
        Vec_PtrPush(vNodes, pObj_g);
      }
    }
    Vec_PtrPush(vNodes, pObj_f);
    Vec_PtrPush(vTable, vNodes);
  }
  Vec_Ptr_t* vNodes = 0;
  Abc_Obj_t* pEntry = 0;
  Abc_Print(ABC_STANDARD, "\n");
  Vec_PtrForEachEntry(Vec_Ptr_t*, vTable, vNodes, i) {
    Abc_Print(ABC_STANDARD, "n%d:", Abc_ObjId((Abc_Obj_t*)Vec_PtrEntryLast(vNodes)));
    Vec_PtrForEachEntryStop(Abc_Obj_t*, vNodes, pEntry, j, Vec_PtrSize(vNodes) - 1) {
      Abc_Print(ABC_STANDARD, " n%d", Abc_ObjId(pEntry));
    }
    Abc_Print(ABC_STANDARD, "\n");
  }
  Vec_PtrFreeFree(vTable);
  Abc_Print(ABC_STANDARD, "\n");
  Abc_PrintTime(ABC_STANDARD, "Time", Abc_Clock() - clk);
}

int Lsv_Is1Sub(Abc_Ntk_t* pNtk, int pObj_fId, int pObj_gId) {
  // pObj_g merges pObj_f
  Abc_Ntk_t* pNtk_dup = Abc_NtkDup(pNtk);
  Abc_ObjReplace(Abc_NtkObj(pNtk_dup, pObj_fId), Abc_NtkObj(pNtk_dup, pObj_gId));
  if (!Abc_NtkIsAcyclic(pNtk_dup)) {
    Abc_NtkDelete(pNtk_dup);
    return 0;
  }
  
  Abc_Ntk_t* pNtk_dup_strash = Abc_NtkStrash(pNtk_dup, 0, 1, 0);
  Abc_NtkDelete(pNtk_dup);
  int result = Lsv_NtkCecFraig(pNtk_dup_strash, pNtk);
  if (result) {
    Abc_NtkDelete(pNtk_dup_strash);
    return 1;
  }
  int i = 0; 
  Abc_Obj_t* pFanout = 0;
  Abc_ObjForEachFanout(Abc_NtkObj(pNtk, pObj_fId), pFanout, i) {
    if (Abc_ObjId(pFanout) >= Abc_NtkObjNum(pNtk_dup_strash)) continue;
    Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup_strash, Abc_ObjId(pFanout));
    if (pObj == NULL) continue;
    if (Abc_ObjFaninId0(pFanout) == pObj_fId) Abc_ObjXorFaninC(pObj, 0);
    else Abc_ObjXorFaninC(pObj, 1);
  }
  int result2 = Lsv_NtkCecFraig(pNtk_dup_strash, pNtk);
  Abc_NtkDelete(pNtk_dup_strash);
  
  return result2;
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

ABC_NAMESPACE_IMPL_END