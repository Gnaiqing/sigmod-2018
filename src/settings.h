#pragma once

#define INPUT_FILE "small.complete"

#ifndef NDEBUG
    #define STATISTICS
    #define LOAD_FROM_FILE INPUT_FILE
    #define CHECK_ERRORS
#endif

#define MEASURE_REAL_TIME
#define STATISTICS

//#define SORT_JOINS_BY_SIZE
//#define TRANSPOSE_RELATIONS

#define USE_HASH_INDEX
//#define USE_SORT_INDEX

#ifdef USE_SORT_INDEX
    #define FILTER_ITERATOR SortFilterIterator
#else
    #define FILTER_ITERATOR FilterIterator
#endif

#define QUERY_NUM_THREADS 20
