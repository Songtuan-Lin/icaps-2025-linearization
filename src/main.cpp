//
// Created by u6162630 on 10/24/24.
//
#include "Model.h"
#include "linearizer.h"

int main(int argc, char** argv) {
    string file_path = argv[1];
    Model *htn = setup_model(file_path);
    ofstream o;
    ComplexInference(htn, false, o, true);
    return 0;
}