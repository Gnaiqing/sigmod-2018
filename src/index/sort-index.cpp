#include "sort-index.h"
#include "../relation/column-relation.h"

#include <cstring>
#include <algorithm>

struct RadixTraitsRowEntry
{
    static const int nBytes = 12;
    int kth_byte(const RowEntry &x, int k) {
        if (k >= 8) return (x.value >> ((k - 8) * 8)) & 0xFF;
        return (x.row >> (k * 8)) & 0xFF;
    }
    bool compare(const RowEntry &x, const RowEntry &y) {
        return x < y;
    }
};

SortIndex::SortIndex(ColumnRelation& relation, uint32_t column)
        : Index(relation, column), data(static_cast<size_t>(relation.getRowCount()))
{

}

void SortIndex::build()
{
    if (this->buildStarted.test_and_set()) return;

    auto rows = static_cast<int32_t>(this->data.size());
    for (int i = 0; i < rows; i++)
    {
        auto value = this->relation.getValue(static_cast<size_t>(i), this->column);
        this->data[i].value = value;
        this->data[i].row = static_cast<uint32_t>(i);
    }
    std::sort(this->data.begin(), this->data.end());
    //kx::radix_sort(this->data.begin(), this->data.end(), RadixTraitsRowEntry());

    this->minValue = this->data[0].value;
    this->maxValue = this->data.back().value;

    this->buildCompleted = true;
}
