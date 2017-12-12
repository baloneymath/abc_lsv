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
extern "C" int*       Abc_NtkVerifySimulatePattern(Abc_Ntk_t* pNtk, int* pModel);
extern "C" void       Abc_NtkVerifyReportError( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int * pModel );

// lsv functions
void  Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk);
int   Lsv_Is1Sub(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int fId, int gId, int nSimIter); 
int   Lsv_NtkSimVerifyPattern(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int* pModel);
int   Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int nSimIter);
int   Lsv_NtkCecFraigPartAuto(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int nSimIter);
void  Lsv_Ntk1SubDump(Vec_Ptr_t* vTable, Vec_Ptr_t* vTable2, Abc_VerbLevel level);
void  Lsv_Ntk1SubDumpFile(Vec_Ptr_t* vTable, Vec_Ptr_t* vTable2, char* filename);

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
  Vec_Ptr_t* vTable2 = Vec_PtrStart(0);
  Abc_Ntk_t* pNtk_dup = Abc_NtkDup(pNtk);
  Vec_Int_t* vWhichFanin = Vec_IntStart(0);
  Abc_AigForEachAnd(pNtk, pObj_f, i) {
    int fId = Abc_ObjId(pObj_f);
    Vec_Ptr_t* vNodes = Vec_PtrStart(0);
    Vec_Int_t* vComps = Vec_IntStart(0);
    Abc_NtkForEachPi(pNtk, pObj_g, j) {
      // merge g to f
      int gId = Abc_ObjId(pObj_g);
      Abc_Obj_t* pFanout = 0;
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        if (Abc_ObjFaninId0(pObj) == fId) {
          pObj->vFanins.pArray[0] = gId;
          Vec_IntPush(vWhichFanin, 0);
        }
        else {
          pObj->vFanins.pArray[1] = gId;
          Vec_IntPush(vWhichFanin, 1);
        }
      }
      // check1sub
      Abc_Ntk_t* pNtk_dup_strash = Abc_NtkStrash(pNtk_dup, 0, 0, 0);
      int retValue = Lsv_Is1Sub(pNtk, pNtk_dup_strash, fId, gId, 2 * Abc_NtkObjNum(pNtk));
      if (retValue == 1) {
        Vec_PtrPush(vNodes, pObj_g);
        Vec_IntPush(vComps, 0);
      }
      else if (retValue == 2) {
        Vec_PtrPush(vNodes, pObj_g);
        Vec_IntPush(vComps, 1);
      }
      else if (retValue == 3) {
        Vec_PtrPush(vNodes, pObj_g);
        Vec_IntPush(vComps, 0);
        Vec_PtrPush(vNodes, pObj_g);
        Vec_IntPush(vComps, 1);
      }
      Abc_NtkDelete(pNtk_dup_strash);
      // recover
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        pObj->vFanins.pArray[Vec_IntEntry(vWhichFanin, k)] = fId;
      }
      Vec_IntClear(vWhichFanin);
    }
    Abc_AigForEachAnd(pNtk, pObj_g, j) {
      int gId = Abc_ObjId(pObj_g);
      if (fId == gId) continue;
      // merge g to f
      Abc_Obj_t* pFanout = 0;
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        if (Abc_ObjFaninId0(pObj) == fId) {
          pObj->vFanins.pArray[0] = gId;
          Vec_IntPush(vWhichFanin, 0);
        }
        else {
          pObj->vFanins.pArray[1] = gId;
          Vec_IntPush(vWhichFanin, 1);
        }
      }
      if (Abc_NtkIsAcyclic(pNtk_dup)) {
        // check 1sub
        Abc_Ntk_t* pNtk_dup_strash = Abc_NtkStrash(pNtk_dup, 0, 0, 0);
        int retValue = Lsv_Is1Sub(pNtk, pNtk_dup_strash, fId, gId, 2 * Abc_NtkObjNum(pNtk));
        if (retValue == 1) {
          Vec_PtrPush(vNodes, pObj_g);
          Vec_IntPush(vComps, 0);
        }
        else if (retValue == 2) {
          Vec_PtrPush(vNodes, pObj_g);
          Vec_IntPush(vComps, 1);
        }
        else if (retValue == 3) {
          Vec_PtrPush(vNodes, pObj_g);
          Vec_IntPush(vComps, 0);
          Vec_PtrPush(vNodes, pObj_g);
          Vec_IntPush(vComps, 1);
        }
        Abc_NtkDelete(pNtk_dup_strash);
      }
      // recover
      Abc_ObjForEachFanout(pObj_f, pFanout, k) {
        Abc_Obj_t* pObj = Abc_NtkObj(pNtk_dup, Abc_ObjId(pFanout));
        pObj->vFanins.pArray[Vec_IntEntry(vWhichFanin, k)] = fId;
      }
      Vec_IntClear(vWhichFanin);
    }
    if (Vec_PtrSize(vNodes)) {
      Vec_PtrPush(vNodes, pObj_f);
      Vec_PtrPush(vTable, vNodes);
      Vec_PtrPush(vTable2, vComps);
    }
  }
  Vec_IntFree(vWhichFanin);
  Abc_NtkDelete(pNtk_dup);
  
  // print result
  char* filename = Abc_NtkName(pNtk);
  strcat(filename, ".log");
  Lsv_Ntk1SubDump(vTable, vTable2, ABC_STANDARD);
  Lsv_Ntk1SubDumpFile(vTable, vTable2, filename);
  Vec_PtrFreeFree(vTable);
  Vec_PtrFreeFree(vTable2);
  Abc_PrintTime(ABC_STANDARD, "Time", Abc_Clock() - clk);
}

int Lsv_Is1Sub(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int fId, int gId, int nSimIter) {
  // pObj_g merges pObj_f
  int retValue = 0;
  assert(Abc_NtkIsStrash(pNtk1) && Abc_NtkIsStrash(pNtk2));
  if (Lsv_NtkCecFraig(pNtk1, pNtk2, nSimIter)) retValue += 1;
  int i = 0; 
  Abc_Obj_t* pFanout = 0;
  Abc_ObjForEachFanout(Abc_NtkObj(pNtk1, fId), pFanout, i) {
    if (Abc_ObjId(pFanout) >= Abc_NtkObjNum(pNtk2)) continue;
    Abc_Obj_t* pTmp = Abc_NtkObj(pNtk2, Abc_ObjId(pFanout));
    assert (pTmp != 0);
    if (Abc_ObjFaninId0(pFanout) == fId) Abc_ObjXorFaninC(pTmp, 0);
    else Abc_ObjXorFaninC(pTmp, 1);
  }
  return Lsv_NtkCecFraig(pNtk1, pNtk2, nSimIter) ? (retValue + 2) : retValue;
  // 0: not 1sub; 1: f merge by g; 2: f merge by not g; 3: f merge by both
}

int Lsv_NtkSimVerifyPattern(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int* pModel) {
  assert(Abc_NtkCiNum(pNtk1) == Abc_NtkCiNum(pNtk2));
  assert(Abc_NtkCoNum(pNtk1) == Abc_NtkCoNum(pNtk2));
  int* pValues1 = Abc_NtkVerifySimulatePattern(pNtk1, pModel);
  int* pValues2 = Abc_NtkVerifySimulatePattern(pNtk2, pModel);
  int retValue = 1;
  for (int i = 0; i < Abc_NtkCoNum(pNtk1); ++i) {
    if (pValues1[i] != pValues2[i]) {
      retValue = 0;
      break;
    }
  }
  ABC_FREE(pValues1);
  ABC_FREE(pValues2);
  return retValue;
}

int Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int nSimIter) {
  // get the miter of the two networks
  Abc_Ntk_t* pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 0, 0, 0);
  if (pMiter == NULL) {
    Abc_Print(ABC_ERROR, "Miter computation has failed.\n");
    return 0;
  }
  int retValue = 0;
  // handle trivial case
  retValue = Abc_NtkMiterIsConstant(pMiter);
  if (retValue == 0 || retValue == 1) {
    Abc_NtkDelete(pMiter);
    return retValue;
  }
  // simulate
  int simValue[Abc_NtkPiNum(pMiter)];
  for (int t = 0; t < nSimIter; ++t) {
    for (int j = 0; j < Abc_NtkPiNum(pMiter); ++j)
      simValue[j] = (rand() & 0x1);
    int* pValues = Abc_NtkVerifySimulatePattern(pMiter, simValue);
    if (pValues[0]) {
      ABC_FREE(pValues);
      Abc_NtkDelete(pMiter);
      return 0;
    }
  }
  // solve the CNF using the SAT solver
  Prove_Params_t Params, *pParams = &Params;
  Prove_ParamsSetDefault(pParams);
  pParams->nItersMax = 5;
  retValue = Abc_NtkMiterProve(&pMiter, pParams);
  Abc_NtkDelete(pMiter);
  return retValue;
}

int Lsv_NtkCecFraigPartAuto(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2, int nSimIter) {
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
    int simValue[Abc_NtkPiNum(pMiterPart)];
    for (int t = 0; t < nSimIter; ++t) {
      for (int j = 0; j < Abc_NtkPiNum(pMiterPart); ++j)
        simValue[j] = (rand() & 0x1);
      int* pValues = Abc_NtkVerifySimulatePattern(pMiterPart, simValue);
      if (pValues[0]) {
        Abc_NtkDelete(pMiterPart);
        return 0;
      }
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

void Lsv_Ntk1SubDump(Vec_Ptr_t* vTable, Vec_Ptr_t* vTable2, Abc_VerbLevel level) {
  assert(Vec_PtrSize(vTable) == Vec_PtrSize(vTable2));
  int i = 0, j = 0;
  Vec_Ptr_t* vNodes = 0;
  Abc_Obj_t* pEntry = 0;
  Abc_Print(level, "\n");
  Vec_PtrForEachEntry(Vec_Ptr_t*, vTable, vNodes, i) {
    Abc_Print(level, "%s:", Abc_ObjName((Abc_Obj_t*)Vec_PtrEntryLast(vNodes)));
    Vec_PtrForEachEntryStop(Abc_Obj_t*, vNodes, pEntry, j, Vec_PtrSize(vNodes) - 1) {
      if (Vec_IntEntry((Vec_Int_t*)Vec_PtrEntry(vTable2, i), j)) Abc_Print(level, " -%s", Abc_ObjName(pEntry));
      else Abc_Print(level, "  %s", Abc_ObjName(pEntry));
    }
    Abc_Print(level, "\n");
  }
  Abc_Print(level, "\n");
}

void Lsv_Ntk1SubDumpFile(Vec_Ptr_t* vTable, Vec_Ptr_t* vTable2, char* filename) {
  assert(Vec_PtrSize(vTable) == Vec_PtrSize(vTable2));
  FILE* fp = fopen(filename, "w");
  int i = 0, j = 0;
  Vec_Ptr_t* vNodes = 0;
  Abc_Obj_t* pEntry = 0;
  Vec_PtrForEachEntry(Vec_Ptr_t*, vTable, vNodes, i) {
    fprintf(fp, "%s:", Abc_ObjName((Abc_Obj_t*)Vec_PtrEntryLast(vNodes)));
    Vec_PtrForEachEntryStop(Abc_Obj_t*, vNodes, pEntry, j, Vec_PtrSize(vNodes) - 1) {
      if (Vec_IntEntry((Vec_Int_t*)Vec_PtrEntry(vTable2, i), j)) fprintf(fp, " -%s", Abc_ObjName(pEntry));
      else fprintf(fp, "  %s", Abc_ObjName(pEntry));
    }
    fprintf(fp, " \n");
  }
  fclose(fp);
}

ABC_NAMESPACE_IMPL_END