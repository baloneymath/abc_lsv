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
#include <vector>
using namespace std;

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
extern "C" void Abc_NtkCecSat( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );
extern "C" void Abc_NtkCecFraig( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );
extern "C" void Abc_NtkCecFraigPart( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nPartSize, int fVerbose );
extern "C" void Abc_NtkCecFraigPartAuto( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );

int Lsv_Is1Sub(Abc_Ntk_t* pNtk, int pObj_fId, int pObj_gId); 
int Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2);
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

void Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk) {
  assert(Abc_NtkIsTopo(pNtk));
  Abc_Obj_t* pObj_f = 0; // to be merged
  Abc_Obj_t* pObj_g = 0; // to resubstitude someone
  
  //Aig_Man_t* pAig = Abc_NtkToDar(pNtk, 0, 0);
  //Cnf_Dat_t* pCnf = Cnf_Derive(pAig, Aig_ManCoNum(pAig));
  //sat_solver* pSat = (sat_solver*)Cnf_DataWriteIntoSolver(pCnf, 1, 0);
  //int status = sat_solver_solve(pSat, NULL, NULL, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0);

  int i = 0, j = 0;
  Abc_NtkForEachNode(pNtk, pObj_f, i) {
    int flag = 0;
    vector<int> tmp;
    Abc_NtkForEachNodeStop(pNtk, pObj_g, j, Abc_ObjId(pObj_f)) {
      if (Lsv_Is1Sub(pNtk, Abc_ObjId(pObj_f), Abc_ObjId(pObj_g))) {
        flag = 1;
        tmp.push_back(Abc_ObjId(pObj_g));
      }
    }
    if (flag) {
      Abc_Print(ABC_STANDARD, "n%d:", Abc_ObjId(pObj_f));
      for (int k = 0; k < tmp.size(); ++k) Abc_Print(ABC_STANDARD, " n%d", tmp[k]);
      Abc_Print(ABC_STANDARD, "\n");
    }
  }
  Abc_Print(ABC_STANDARD, "\n");
}

int Lsv_Is1Sub(Abc_Ntk_t* pNtk, int pObj_fId, int pObj_gId) {
  // pObj_g merges pObj_f
  Abc_Ntk_t* pNtk_dup = Abc_NtkDup(pNtk);
  //printf("%d %d\n", Abc_NtkNodeNum(pNtk), Abc_NtkNodeNum(pNtk_dup));
  Abc_ObjReplace(Abc_NtkObj(pNtk_dup, pObj_fId), Abc_NtkObj(pNtk_dup, pObj_gId));
  //printf("%d %d\n", Abc_NtkNodeNum(pNtk), Abc_NtkNodeNum(pNtk_dup));
  int result = Lsv_NtkCecFraig(pNtk_dup, pNtk);
  //Abc_NtkCecFraig(pNtk, pNtk_dup, 0, 0);
  Abc_NtkDelete(pNtk_dup);
  return result;
  //return 1;
}

int Lsv_NtkCecFraig(Abc_Ntk_t* pNtk1, Abc_Ntk_t* pNtk2) {
  Prove_Params_t Params, *pParams = &Params;
  Abc_Ntk_t *pMiter = 0;
  int RetValue;
  // get the miter of the two networks
  pMiter = Abc_NtkMiter(pNtk1, pNtk2, 1, 0, 0, 0);
  if (pMiter == NULL) {
    Abc_Print(ABC_ERROR, "Miter computation has failed.\n");
    return 0;
  }
  // handle trivial case
  RetValue = Abc_NtkMiterIsConstant(pMiter);
  if (RetValue == 0 || RetValue == 1) {
    Abc_NtkDelete(pMiter);
    return RetValue;
  }
  // solve the CNF using the SAT solver
  Prove_ParamsSetDefault(pParams);
  pParams->nItersMax = 5;
  RetValue = Abc_NtkIvyProve(&pMiter, pParams);
  Abc_NtkDelete(pMiter);
  return RetValue;
}

ABC_NAMESPACE_IMPL_END