#include "sort-index-iterator.h"
#include "../database.h"
#include "../index/sort-index.h"
#include "primary-index-iterator.h"

#include <algorithm>
#include <cmath>

SortIndexIterator::SortIndexIterator(ColumnRelation* relation, uint32_t binding, const std::vector<Filter>& filters)
        : IndexIterator(relation, binding, filters)
{
    if (!this->filters.empty())
    {
        this->index = this->getIndex(this->iteratedSelection.relation, this->iteratedSelection.column);
        if (this->index != nullptr)
        {
            this->createIterators(this->filters[0], &this->start, &this->end);
        }
    }

    this->start--;
    this->originalStart = this->start;
}

SortIndexIterator::SortIndexIterator(ColumnRelation* relation, uint32_t binding, const std::vector<Filter>& filters,
                                     RowEntry* start, RowEntry* end,
                                     Selection iteratedSelection)
        : IndexIterator(relation, binding, filters, start, end, iteratedSelection)
{

}

bool SortIndexIterator::getNext()
{
    this->start++;

    for (; this->start < this->end; this->start++)
    {
        this->rowIndex = this->start->row;
        if (this->passesFilters())
        {
#ifdef COLLECT_JOIN_SIZE
            this->rowCount++;
#endif
            return true;
        }
    }

    return false;
}

SortIndex* SortIndexIterator::getIndex(uint32_t relation, uint32_t column)
{
    return database.getSortIndex(relation, column);
}

bool SortIndexIterator::skipSameValue(const Selection& selection)
{
    if (selection == this->iteratedSelection)
    {
        uint64_t value = this->relation->getValue(this->rowIndex, this->iteratedSelection.column);
        for (; this->start < this->end; this->start++)
        {
            this->rowIndex = this->start->row;
            uint64_t newValue = this->relation->getValue(this->rowIndex, this->iteratedSelection.column);
            if (newValue == value) continue;
            if (this->passesFilters())
            {
#ifdef COLLECT_JOIN_SIZE
                this->rowCount++;
#endif
                return true;
            }
        }

        return false;
    }
    return this->getNext();
}

bool SortIndexIterator::passesFilters()
{
    for (int i = this->startFilterIndex; i < this->filterSize; i++)
    {
        auto& filter = this->filters[i];
#ifdef COMPILE_FILTERS
        if (!filter.evaluator(this->relation->getValue(filter.selection, this->rowIndex))) return false;
#else
        if (!passesFilter(filter, this->relation->getValue(filter.selection, this->rowIndex))) return false;
#endif
    }

    return true;
}

std::unique_ptr<Iterator> SortIndexIterator::createIndexedIterator(std::vector<std::unique_ptr<Iterator>>& container,
                                                                      const Selection& selection)
{
    if (database.getPrimaryIndex(selection.relation, selection.column) != nullptr)
    {
        return std::make_unique<PrimaryIndexIterator>(this->relation, this->binding, this->filters);
    }
    else return std::make_unique<SortIndexIterator>(this->relation, this->binding, this->filters,
                                                    this->originalStart,
                                                    this->end,
                                                    this->iteratedSelection);
}

RowEntry* SortIndexIterator::findNextValue(const Selection& selection, uint64_t value)
{
    auto ptr = this->start;
    while (ptr < this->index->end && ptr->value == value)
    {
        ptr++;
    }

    return ptr;
}
