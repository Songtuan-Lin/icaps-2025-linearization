project(linearizer)

file(GLOB LINEAREIZER_SOURCE_FILES
        "src/*.cpp"
        "../Model.cpp"
        "../PrecsEffs.cpp"
        "../ProgressionNetwork.cpp" 
        "../Util.cpp" 
        "../Debug.cpp" 
        "../Invariants.cpp"
)

add_library(linearizer
    ${LINEAREIZER_SOURCE_FILES}
)

target_link_libraries(linearizer
    PUBLIC
        intDataStructures
)

target_include_directories(linearizer
    PUBLIC
        ${linearization_SOURCE_DIR}/
        ${PROJECT_SOURCE_DIR}/include
)