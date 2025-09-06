cmake_minimum_required(VERSION 3.14)
project(cyaronc CXX C)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

if(LLVM_LINK_LLVM_DYLIB)
    set(llvm_libs LLVM)
else()
    llvm_map_components_to_libnames(llvm_libs
        Core
        Support
        Analysis
        Target
        MC
        MCParser
        MCDisassembler
        AsmParser
        AsmPrinter
        IRReader
        BitWriter
        AllTargetsInfos
        AllTargetsMC
        AllTargetsAsmParsers
        AllTargetsAsmPrinters
        AllTargetsDisassemblers
        AllTargetsCodeGens
    )
endif()

add_executable(cyaronc cyaronc.cpp)

target_link_libraries(cyaronc PRIVATE ${llvm_libs})