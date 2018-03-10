#include "database.h"

uint32_t Database::getGlobalColumnId(uint32_t relation, uint32_t column)
{
    return this->relations[relation].cumulativeColumnId + column;
}

HashIndex& Database::getHashIndex(uint32_t relation, uint32_t column)
{
    return *this->hashIndices[this->getGlobalColumnId(relation, column)];
}

SortIndex& Database::getSortIndex(uint32_t relation, uint32_t column)
{
    return *this->sortIndices[this->getGlobalColumnId(relation, column)];
}
