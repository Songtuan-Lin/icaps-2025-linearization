//
// Created by Conny Olz on 05.08.21 based on code by Maximilian Borowiec.
//

#ifndef PANDAPIENGINE_PRECSEFFS_H
#define PANDAPIENGINE_PRECSEFFS_H

#endif //PANDAPIENGINE_PRECSEFFS_H

#include "Model.h"

using namespace std;

namespace progression {
    void computeEffectsAndPreconditions(Model* model, vector<int>* poss_eff_positive, vector<int>* poss_eff_negative,
                                        vector<int>* eff_positive, vector<int>* eff_negative, vector<int>* preconditions, vector<int>* poss_preconditions, int amount_compound_tasks);
    void computeEffectsOfVariable(Model* model, int var, vector<int>* poss_eff_positive, vector<int>* poss_eff_negative,
                                  vector<int>* eff_positive, vector<int>* eff_negative, int amount_compound_tasks, int** orderedSubTasks);
    void computeEffectsOfMethodVariable(Model* model, int var, vector<int>* poss_eff_positive, vector<int>* poss_eff_negative,
                                  vector<int>* eff_positive, vector<int>* eff_negative, int amount_compound_tasks, int** orderedSubTasks);
    void computeEffectsOfPOMethodVariable(Model* model, int var, vector<int>* poss_eff_positive, vector<int>* poss_eff_negative,
                                          vector<int>* eff_positive, vector<int>* eff_negative, int amount_compound_tasks,
                                          vector<vector<vector<bool>>> transSuccessors);
    void computeExecutabilityRelaxedProconditions(Model* model, int var, vector<int>* preconditions,
                                                  int amount_compound_tasks, int** orderedSubTasks);
    void computeRelaxedMethodPreconditions(Model* model, int var, vector<int>* preconditions,
                                           int amount_compound_tasks, int** orderedSubTasks);
    void computeRelaxedPOMethodPreconditions(Model* model, int var, vector<int>* preconditions, vector<int>* poss_preconditions,
                                           int amount_compound_tasks, vector<vector<vector<bool>>> transSuccessors);
    void orderSubTasks(Model* model, int** orderedSubTasks);
    vector<vector<vector<bool>>> calculateTransitiveClosure(Model* model);
    void printResults(Model* model, vector<int>* preconditions, vector<int>* poss_eff_positive, vector<int>* eff_positive,
                      vector<int>* poss_eff_negative, vector<int>* eff_negative, int amount_compound_tasks);
    void printElementWithName(Model* model, vector<int> container, ofstream& File);
    void exploitInvariants(Model* model);
    // void computeHierarchyReachability(Model* model);
    // void transformPrimitiveAddEffectsToArray(Model* models);
}
