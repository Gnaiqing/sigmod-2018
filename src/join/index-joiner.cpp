#include <iostream>
#include "index-joiner.h"

IndexJoiner::IndexJoiner(Iterator* left, Iterator* right, uint32_t leftIndex, Join& join)
        : Joiner(left, right, leftIndex, join),
          leftSel(this->join[0].selections[this->leftIndex]),
          rightSel(this->join[0].selections[this->rightIndex])
{

}

bool IndexJoiner::getNext()
{
    while (true)
    {
        if (!this->right->getNext())
        {
            if (!this->left->getNext())
            {
                return false;
            }
            uint64_t value = this->left->getValue(this->leftSel);
            this->right->iterateValue(this->rightSel, value);
            continue;
        }

        bool ok = true;
        for (int i = 1; i < joinSize; i++)
        {
            if (this->left->getValue(this->join[i].selections[this->leftIndex]) !=
                this->right->getValue(this->join[i].selections[this->rightIndex]))
            {
                ok = false;
                break;
            }
        }
        if (ok) return true;
    }
}

uint64_t IndexJoiner::getValue(const Selection& selection)
{
    uint64_t value;
    if (this->left->getValueMaybe(selection, value)) return value;
    return this->right->getValue(selection);
}

uint64_t IndexJoiner::getColumn(uint32_t column)
{
    if (column < this->leftColSize)
    {
        return this->left->getColumn(column);
    }
    return this->right->getColumn(column - this->leftColSize);
}

bool IndexJoiner::getValueMaybe(const Selection& selection, uint64_t& value)
{
    if (this->left->getValueMaybe(selection, value)) return true;
    return this->right->getValueMaybe(selection, value);
}

void IndexJoiner::requireSelections(std::unordered_map<SelectionId, Selection>& selections)
{
    for (auto& j: this->join)
    {
        selections[j.selections[0].getId()] = j.selections[0];
        selections[j.selections[1].getId()] = j.selections[1];
    }

    this->left->requireSelections(selections);
    this->right->prepareIndexedAccess();

    this->leftColSize = static_cast<uint32_t>(this->left->getColumnCount());
}

void IndexJoiner::sumRows(std::vector<uint64_t>& results, const std::vector<uint32_t>& columnIds, size_t& count)
{
    std::vector<std::pair<uint32_t, uint32_t>> leftColumns; // column, result index
    std::vector<std::pair<uint32_t, uint32_t>> rightColumns;
    auto colSize = static_cast<int32_t>(columnIds.size());

    for (int i = 0; i < colSize; i++)
    {
        auto column = columnIds[i];
        if (column < this->leftColSize)
        {
            leftColumns.emplace_back(columnIds[i], i);
        }
        else rightColumns.emplace_back(columnIds[i] - this->leftColSize, i);
    }

    while (this->getNext())
    {
        for (auto c: leftColumns)
        {
            results[c.second] += this->left->getColumn(c.first);
        }
        for (auto c: rightColumns)
        {
            results[c.second] += this->right->getColumn(c.first);
        }
        count++;
    }
}

uint32_t IndexJoiner::getColumnForSelection(const Selection& selection)
{
    if (this->left->hasSelection(selection))
    {
        return this->left->getColumnForSelection(selection);
    }
    return this->right->getColumnForSelection(selection) + this->leftColSize;
}

bool IndexJoiner::hasSelection(const Selection& selection)
{
    return this->left->hasSelection(selection) || this->right->hasSelection(selection);
}

void IndexJoiner::fillHashTable(const Selection& hashSelection, const std::vector<Selection>& selections,
                                HashMap<uint64_t, std::vector<uint64_t>>& hashTable)
{
    auto columnMapCols = static_cast<int32_t>(selections.size());
    auto countSub = static_cast<size_t>(selections.size() - 1);

    std::vector<std::pair<uint32_t, uint32_t>> leftColumns; // column, result index
    std::vector<std::pair<uint32_t, uint32_t>> rightColumns;

    for (int i = 0; i < columnMapCols; i++)
    {
        if (this->left->hasSelection(selections[i]))
        {
            leftColumns.emplace_back(this->left->getColumnForSelection(selections[i]), i);
        }
        else rightColumns.emplace_back(this->left->getColumnForSelection(selections[i]), i);
    }

    uint32_t hashColumn = this->getColumnForSelection(hashSelection);
    while (this->getNext())
    {
        uint64_t value = this->getColumn(hashColumn);
        auto& vec = hashTable[value];

        // materialize rows
        vec.resize(vec.size() + columnMapCols);
        auto rowData = &vec.back() - countSub;
        for (auto c: leftColumns)
        {
            rowData[c.second] += this->left->getColumn(c.first);
        }
        for (auto c: rightColumns)
        {
            rowData[c.second] += this->right->getColumn(c.first);
        }
    }
}