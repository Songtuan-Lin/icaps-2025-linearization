//
// Created by u6162630 on 10/24/24.
//
#include "Model.h"
#include "linearizer.h"

void write_sas(string outfile, Model *htn);
void write_action(ofstream &fOut, int i, Model *htn);

int main(int argc, char** argv) {
    string file_path = argv[1];
    Model *htn = setup_model(file_path);
    for (int m =0; m < htn->numMethods; m++) {
        if (!htn->isMethodTotallyOrdered(m)) {
            cout << "Method " << m << " is not TO: " << htn->methodNames[m] << endl;
        }
    }
    ofstream o;
    // Choose between type: random, simple or complex
    Linearize(htn, "complex", false, o);
    //ComplexInference(htn, false, o, true);
    htn->generateMethodRepresentation();
    string outFile = argv[2];
    write_sas(outFile, htn);
    return 0;
}

void write_sas(string outfile, Model *htn) {
    ofstream fOut(outfile);
    fOut << htn->numStateBits << endl;
    for (int i = 0; i < htn->numStateBits; i++) {
        fOut << htn->factStrs[i] << endl;
    }
    fOut << endl << ";; Mutex Groups" << endl;
    fOut << htn->numVars << endl;
    for (int i = 0; i < htn->numVars; i++) {
        fOut << htn->firstIndex[i] << " " << htn->lastIndex[i] << " " << htn->varNames[i] << endl;
    }
    fOut << endl << ";; further strict Mutex Groups" << endl;
    fOut << htn->numStrictMutexes << endl;
    for (int i = 0; i < htn->numStrictMutexes; i++) {
        fOut << htn->strictMutexes[i][0] << " " << htn->strictMutexes[i][1] << " -1" << endl;
    }

    fOut << endl << ";; further non strict Mutex Groups" << endl;
    fOut << htn->numMutexes << endl;
    for (int i = 0; i < htn->numMutexes; i++) {
        fOut << htn->mutexes[i][0] << " " << htn->mutexes[i][1] << " -1" << endl;
    }

    fOut << endl << ";; known invariants" << endl;
    fOut << htn->numInvariants << endl;
    for (int i = 0; i < htn->numInvariants; i++) {
        fOut << htn->invariants[i][0] << " " << htn->invariants[i][1] << " -1" << endl;
    }
    fOut << endl << ";; Actions" << endl;
    fOut << (htn->numActions) << endl;
    for (int i = 0; i < htn->numActions; i++) {
        write_action(fOut, i, htn);
    }
    fOut << endl << ";; initial state" << endl;
    for (int i = 0; i < htn->s0Size; i++) {
        fOut << htn->s0List[i] << " ";
    }
    fOut << "-1" << endl;
    fOut << endl << ";; goal" << endl;
    for (int i = 0; i < htn->gSize; i++) {
        fOut << htn->gList[i] << " ";
    }
    fOut << "-1" << endl;
    fOut << endl << ";; tasks (primitive and abstract)" << endl;
    fOut << htn->numTasks << endl;
    for (int i = 0; i < htn->numTasks; i++) {
        if (htn->isPrimitive[i]) {
            fOut << "0 " << htn->taskNames[i] << endl;
        } else{fOut << "1 " << htn->taskNames[i] << endl;}
    }
    fOut << endl << ";; initial abstract task" << endl;
    fOut << htn->initialTask << endl;
    fOut << endl << ";; methods" << endl;
    fOut << htn->numMethods << endl;
    for (int i = 0; i < htn->numMethods; i++) {
        fOut << htn->methodNames[i] << endl;
        fOut << htn->decomposedTask[i] << endl;
        for (int j = 0; j < htn->numSubTasks[i]; j++) {
            fOut << htn->subTasks[i][j] << " ";
        }
        fOut << "-1" << endl;
        for (int j = 0; j < htn->numOrderings[i]; j++) {
            fOut << htn->ordering[i][j] << " ";
        }
        fOut << "-1" << endl;
    }
}

void write_action(ofstream &fOut, int i, Model *htn) {
    fOut << htn->actionCosts[i] << endl;
    for (int j = 0; j < htn->numPrecs[i]; j++) {
        fOut << htn->precLists[i][j] << " ";
    }
    fOut << "-1" << endl;
    for (int j = 0; j < htn->numAdds[i]; j++) {
        fOut << "0 " << htn->addLists[i][j] << "  ";
    }
    fOut << "-1" << endl;
    for (int j = 0; j < htn->numDels[i]; j++) {
        fOut << "0 " << htn->delLists[i][j] << "  ";
    }
    fOut << "-1" << endl;
}