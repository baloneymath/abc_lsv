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

ABC_NAMESPACE_IMPL_START

void Lsv_Ntk1SubFind(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj = 0;
  int i = 0;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    
  }
}

ABC_NAMESPACE_IMPL_END