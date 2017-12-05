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
extern "C" Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
int Lsv_Is1Sub(Abc_Ntk_t* pNtk, Abc_Obj_t* pObj_f, Abc_Obj_t* pObj_g) {
  // pObj_g merges pObj_f
  
  return 1;
}

void Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj_f = 0; // to be merged
  Abc_Obj_t* pObj_g = 0; // to resubstitude someone
  //Vec_Ptr_t* vNodes = Abc_NtkDfs2(pNtk);
  assert(Abc_NtkIsDfsOrdered(pNtk));
  Abc_Print(ABC_STANDARD, "Abc_NtkIsDfsOrdered: %d\n", Abc_NtkIsDfsOrdered(pNtk));

  //Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
  //Cnf_Dat_t* pCnf = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
  //sat_solver* pSat = (sat_solver*)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
  //int status = sat_solver_solve(pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);
  
  int i = 0, j = 0;
  Abc_NtkForEachNode(pNtk, pObj_f, i) {
    Abc_Print(ABC_STANDARD, "n%d:", Abc_ObjId(pObj_f));
    Abc_NtkForEachNodeStop(pNtk, pObj_g, j, Abc_ObjId(pObj_f)) {
      if (Lsv_Is1Sub(pNtk, pObj_f, pObj_g)) {
        Abc_Print(ABC_STANDARD, " n%d", Abc_ObjId(pObj_g));
      }
    }
    Abc_Print(ABC_STANDARD, "\n");
  }
  printf("\n");
}

ABC_NAMESPACE_IMPL_END