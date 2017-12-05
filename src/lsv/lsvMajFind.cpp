/**CFile****************************************************************

  FileName    [lsvMajFind.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [lsv: Logic Synthesis and Verification PA.]

  Synopsis    [procedure for finding MAJ gates.]

  Author      [Hao Chen]
  
  Affiliation [NTU]

  Date        [14, Oct., 2017.]

***********************************************************************/

////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "base/main/mainInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

bool Lsv_isCompGate(Abc_Obj_t* pObj1, Abc_Obj_t* pObj2) {
  if (Abc_ObjFaninNum(pObj1) == 0 || Abc_ObjFaninNum(pObj2) == 0) return false;
  Abc_Obj_t* pObj1_fanin0 = Abc_ObjFanin0(pObj1);
  Abc_Obj_t* pObj1_fanin1 = Abc_ObjFanin1(pObj1);
  Abc_Obj_t* pObj2_fanin0 = Abc_ObjFanin0(pObj2);
  Abc_Obj_t* pObj2_fanin1 = Abc_ObjFanin1(pObj2);
  if (pObj1_fanin0 == pObj2_fanin0 && pObj1_fanin1 == pObj2_fanin1) {
    return ( Abc_ObjFaninC0(pObj1) ^ Abc_ObjFaninC0(pObj2) ) &
           ( Abc_ObjFaninC1(pObj1) ^ Abc_ObjFaninC1(pObj2) );
  }
  else if (pObj1_fanin0 == pObj2_fanin1 && pObj1_fanin1 == pObj2_fanin0) {
    return ( Abc_ObjFaninC0(pObj1) ^ Abc_ObjFaninC1(pObj2) ) &
           ( Abc_ObjFaninC1(pObj1) ^ Abc_ObjFaninC0(pObj2) );
  }
  return false;
}

bool Lsv_isMajGate(Abc_Obj_t* pObj) {
  if (!Abc_ObjFaninC0(pObj) || !Abc_ObjFaninC1(pObj)) return false;
  Abc_Obj_t* fanin0 = Abc_ObjFanin0(pObj);
  Abc_Obj_t* fanin1 = Abc_ObjFanin1(pObj);
  if (Abc_ObjFaninNum(fanin0) == 0 || Abc_ObjFaninNum(fanin1) == 0) return false;
  int a = 0, b = 0, c = 0;
  Abc_Obj_t *g5 = 0, *g6 = 0;
  
  if ( Lsv_isCompGate(Abc_ObjFanin0(fanin0), fanin1) ) {
    g5 = Abc_ObjFanin0(fanin0);
    g6 = fanin0;
    if (Abc_ObjFaninC0(fanin0)) {
      a = Abc_ObjFaninC1(g6)? -Abc_ObjFaninId1(g6) : Abc_ObjFaninId1(g6);
      b = Abc_ObjFaninC0(g5)? Abc_ObjFaninId0(g5) : -Abc_ObjFaninId0(g5);
      c = Abc_ObjFaninC1(g5)? Abc_ObjFaninId1(g5) : -Abc_ObjFaninId1(g5);
    }
  }
  else if ( Lsv_isCompGate(Abc_ObjFanin1(fanin0), fanin1) ) {
    g5 = Abc_ObjFanin1(fanin0);
    g6 = fanin0;
    if (Abc_ObjFaninC1(fanin0)) {
      a = Abc_ObjFaninC0(g6)? -Abc_ObjFaninId0(g6) : Abc_ObjFaninId0(g6);
      b = Abc_ObjFaninC0(g5)? Abc_ObjFaninId0(g5) : -Abc_ObjFaninId0(g5);
      c = Abc_ObjFaninC1(g5)? Abc_ObjFaninId1(g5) : -Abc_ObjFaninId1(g5);
    }
  }
  else if ( Lsv_isCompGate(Abc_ObjFanin0(fanin1), fanin0) ) {
    g5 = Abc_ObjFanin0(fanin1);
    g6 = fanin1;
    if (Abc_ObjFaninC0(fanin1)) {
      a = Abc_ObjFaninC1(g6)? -Abc_ObjFaninId1(g6) : Abc_ObjFaninId1(g6);
      b = Abc_ObjFaninC0(g5)? Abc_ObjFaninId0(g5) : -Abc_ObjFaninId0(g5);
      c = Abc_ObjFaninC1(g5)? Abc_ObjFaninId1(g5) : -Abc_ObjFaninId1(g5);
    }
  }
  else if ( Lsv_isCompGate(Abc_ObjFanin1(fanin1), fanin0) ) {
    g5 = Abc_ObjFanin1(fanin1);
    g6 = fanin1;
    if (Abc_ObjFaninC1(fanin1)) {
      a = Abc_ObjFaninC0(g6)? -Abc_ObjFaninId0(g6) : Abc_ObjFaninId0(g6);
      b = Abc_ObjFaninC0(g5)? Abc_ObjFaninId0(g5) : -Abc_ObjFaninId0(g5);
      c = Abc_ObjFaninC1(g5)? Abc_ObjFaninId1(g5) : -Abc_ObjFaninId1(g5);
    }
  }
  else return false;
  Abc_Print(ABC_STANDARD, "%d = MAJ(%d, %d, %d)\n", Abc_ObjId(pObj), -a, -b, -c);
  return true;
}

void Lsv_NtkMajFind(Abc_Ntk_t * pNtk) {
  Abc_Obj_t* pObj = 0;
  int i = 0, totalMaj = 0;
  Abc_AigForEachAnd(pNtk, pObj, i) {
    if (Lsv_isMajGate(pObj)) ++totalMaj;
  }
  Abc_NtkForEachPo(pNtk, pObj, i) {
    if (Lsv_isMajGate(pObj)) ++totalMaj;
  }
  Abc_Print(ABC_STANDARD, "# Total MAJ-3 num: %d\n", totalMaj);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

