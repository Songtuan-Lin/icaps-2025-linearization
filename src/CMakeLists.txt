cmake_minimum_required(VERSION 3.13)
set(CMAKE_CXX_STANDARD 17)


set(CMAKE_CXX_STANDARD_REQUIRED ON)

### if no build type is set, it is "Release"
if (NOT CMAKE_BUILD_TYPE OR CMAKE_BUILD_TYPE STREQUAL "")
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "" FORCE)
endif()

project(linearization)

### Project Includes
include_directories("intDataStructures")
add_subdirectory(intDataStructures)
add_subdirectory(linearizer)

file(GLOB main_SRC "*.h" "*.cpp")
 
# create the executable
add_executable (linearization ${main_SRC})
target_compile_options(linearization PUBLIC ${compiler_flags})
target_link_options(linearization PUBLIC ${linker_flags})

target_link_libraries(linearization PUBLIC linearizer)
target_link_libraries(linearization PUBLIC intDataStructures)
