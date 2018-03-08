#pragma once

#include <unordered_map>
#include <vector>

#include "../util.h"

class ColumnRelation;

class HashIndex
{
public:
    HashIndex(ColumnRelation& relation, uint32_t column);
    DISABLE_COPY(HashIndex);

    void build();

    std::unordered_map<uint64_t, std::vector<uint64_t>> hashTable; // value to rowid
    ColumnRelation& relation;
    uint32_t column;
};