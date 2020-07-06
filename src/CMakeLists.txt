set(MODULE_NAME mck)

set(MODULE_DEPENDENCY
    ${PROJECT_DEPENDENCY}
    )

file(GLOB MODULE_SRC
    "${CMAKE_CURRENT_LIST_DIR}/*.cpp"
    )

add_library(${MODULE_NAME} ${MODULE_SRC})
target_link_libraries(${MODULE_NAME} ${MODULE_DEPENDENCY})
