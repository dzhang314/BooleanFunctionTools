// C++ Standard Library Headers
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <vector>

// OpenMP Headers
#include <omp.h>


////////////////////////////////////////////////////////////////////////////////


struct BitSet {

    std::uint_fast8_t data;

    explicit constexpr BitSet(std::uint_fast8_t data) noexcept :
        data(data) {}

    constexpr bool does_not_intersect(BitSet rhs) const noexcept {
        return (data & rhs.data) == 0;
    }

    constexpr BitSet operator&(BitSet rhs) const noexcept {
        return BitSet{static_cast<std::uint_fast8_t>(data & rhs.data)};
    }

    constexpr bool is_proper_subset_of(BitSet rhs) const noexcept {
        return ((data & rhs.data) == data) && (rhs.data & ~data);
    }

    constexpr int cardinality() const noexcept {
        return __builtin_popcount(data);
    }

}; // struct BitSet


struct BitSetIterator {

    std::uint_fast8_t data;

    explicit constexpr BitSetIterator(std::uint_fast8_t data) noexcept :
        data(data) {}

    constexpr BitSetIterator &operator++() noexcept {
        ++data;
        return *this;
    }

    constexpr bool operator==(BitSetIterator rhs) const noexcept {
        return data == rhs.data;
    }

    constexpr BitSet operator*() const noexcept {
        return BitSet{data};
    }

}; // struct BitSetIterator


struct SingletonIterator {

    std::uint_fast8_t data;

    explicit constexpr SingletonIterator(std::uint_fast8_t data) noexcept :
        data(data) {}

    constexpr SingletonIterator &operator++() noexcept {
        data <<= 1;
        return *this;
    }

    constexpr bool operator==(SingletonIterator rhs) const noexcept {
        return data == rhs.data;
    }

    constexpr BitSet operator*() const noexcept {
        return BitSet{data};
    }

}; // struct SingletonIterator


struct AllBitSets {

    std::uint_fast8_t length;

    constexpr BitSetIterator begin() const noexcept {
        return BitSetIterator{static_cast<std::uint_fast8_t>(0)};
    }

    constexpr BitSetIterator end() const noexcept {
        return BitSetIterator{static_cast<std::uint_fast8_t>(1 << length)};
    }

}; // struct AllBitSets


struct SingletonBitSets {

    std::uint_fast8_t length;

    constexpr SingletonIterator begin() const noexcept {
        return SingletonIterator{static_cast<std::uint_fast8_t>(1)};
    }

    constexpr SingletonIterator end() const noexcept {
        return SingletonIterator{static_cast<std::uint_fast8_t>(1 << length)};
    }

}; // struct SingletonBitSets


////////////////////////////////////////////////////////////////////////////////


struct BitString {

    std::uint_fast8_t data;

    explicit constexpr BitString(std::uint_fast8_t data) noexcept :
        data(data) {}

    constexpr BitString operator&(BitSet rhs) const noexcept {
        return BitString{static_cast<std::uint_fast8_t>(data & rhs.data)};
    }

    constexpr BitString operator^(BitSet rhs) const noexcept {
        return BitString{static_cast<std::uint_fast8_t>(data ^ rhs.data)};
    }

    constexpr bool operator==(BitString rhs) const noexcept {
        return data == rhs.data;
    }

}; // struct BitString


struct BitStringIterator {

    std::uint_fast8_t data;

    explicit constexpr BitStringIterator(std::uint_fast8_t data) noexcept :
        data(data) {}

    constexpr BitStringIterator &operator++() noexcept {
        ++data;
        return *this;
    }

    constexpr bool operator==(BitStringIterator rhs) const noexcept {
        return data == rhs.data;
    }

    constexpr BitString operator*() const noexcept {
        return BitString{data};
    }

}; // struct BitStringIterator


struct AllBitStrings {

    std::uint_fast8_t length;

    constexpr BitStringIterator begin() const noexcept {
        return BitStringIterator{static_cast<std::uint_fast8_t>(0)};
    }

    constexpr BitStringIterator end() const noexcept {
        return BitStringIterator{static_cast<std::uint_fast8_t>(1 << length)};
    }

}; // struct AllBitStrings


////////////////////////////////////////////////////////////////////////////////


struct BooleanFunction {

    std::uint_fast64_t data;

    constexpr bool operator()(BitString x) const noexcept {
        return (data >> x.data) & 1;
    }

}; // struct BooleanFunction


////////////////////////////////////////////////////////////////////////////////


template <int N>
bool is_certificate(BooleanFunction f, BitString x, BitSet s) {
    for (const BitString y : AllBitStrings{N}) {
        if ((x & s) == (y & s) && f(x) != f(y)) { return false; }
    }
    return true;
}


template <int N>
int certificate_complexity(BooleanFunction f, BitString x) {
    int result = N;
    for (const BitSet s : AllBitSets{N}) {
        if (is_certificate<N>(f, x, s)) {
            result = std::min(result, s.cardinality());
        }
    }
    return result;
}


template <int N>
int certificate_complexity(BooleanFunction f) {
    int result = 0;
    for (const BitString x : AllBitStrings{N}) {
        result = std::max(result, certificate_complexity<N>(f, x));
    }
    return result;
}


////////////////////////////////////////////////////////////////////////////////


template <int N>
int sensitivity(BooleanFunction f, BitString x) {
    int result = 0;
    const bool fx = f(x);
    for (const BitSet s : SingletonBitSets{N}) {
        if (fx != f(x ^ s)) { ++result; }
    }
    return result;
}


template <int N>
int sensitivity(BooleanFunction f) {
    int result = 0;
    for (const BitString x : AllBitStrings{N}) {
        result = std::max(result, sensitivity<N>(f, x));
    }
    return result;
}


////////////////////////////////////////////////////////////////////////////////


template <int N>
std::vector<BitSet> sensitive_blocks(BooleanFunction f, BitString x) {
    std::vector<BitSet> result{};
    const bool fx = f(x);
    for (const BitSet s : AllBitSets{N}) {
        if (fx != f(x ^ s)) { result.push_back(s); }
    }
    return result;
}


bool is_minimal(const std::vector<BitSet> &sets, BitSet s) {
    for (const BitSet t : sets) {
        if (t.is_proper_subset_of(s)) { return false; }
    }
    return true;
}


template <int N>
std::vector<BitSet> minimal_sensitive_blocks(BooleanFunction f, BitString x) {
    const std::vector<BitSet> blocks = sensitive_blocks<N>(f, x);
    std::vector<BitSet> result{};
    for (const BitSet block : blocks) {
        if (is_minimal(blocks, block)) { result.push_back(block); }
    }
    return result;
}


template <int N>
int block_sensitivity(BooleanFunction f, BitString x) {
    const std::vector<BitSet> blocks = minimal_sensitive_blocks<N>(f, x);
    const int num_blocks = blocks.size();
    const int subset_max = 1 << num_blocks;
    int result = 0;
    for (int subset = 0; subset < subset_max; ++subset) {
        BitSet acc{0};
        int candidate_sensitivity = 0;
        for (int i = 0; i < num_blocks; ++i) {
            if (((subset >> i) & 1)) {
                const BitSet block = blocks[i];
                if (acc.does_not_intersect(block)) {
                    acc.data |= block.data;
                    ++candidate_sensitivity;
                }
            }
        }
        result = std::max(result, candidate_sensitivity);
    }
    return result;
}


template <int N>
int block_sensitivity(BooleanFunction f) {
    int result = 0;
    for (const BitString x : AllBitStrings{N}) {
        result = std::max(result, block_sensitivity<N>(f, x));
    }
    return result;
}


////////////////////////////////////////////////////////////////////////////////


template <int complexity_measure(BooleanFunction), int N>
void write_data_file(const std::string &name) {

    std::cout << "Allocating data array..." << std::endl;
    constexpr std::uint64_t NUM_FUNCS = 1ULL << (1 << N);
    std::uint8_t *const results = new std::uint8_t[NUM_FUNCS];

    std::cout << "Computing " << name << " of all Boolean functions on "
              << N << " variables..." << std::endl;
    #pragma omp parallel for
    for (std::uint64_t f = 0; f < NUM_FUNCS; ++f) {
        results[f] = static_cast<std::uint8_t>(
            complexity_measure(BooleanFunction{f})
        );
    }

    const std::string filename = name + std::to_string(N) + ".dat";
    std::cout << "Writing data file " << filename << "..." << std::endl;
    const char *data = reinterpret_cast<const char *>(results);
    const char *const end = data + NUM_FUNCS * sizeof(std::uint8_t);
    std::ofstream writer{filename, std::ios::binary};
    while (data + 100'000'000 < end) {
        writer.write(data, 100'000'000);
        writer.flush();
        data += 100'000'000;
    }
    writer.write(data, end - data);

    if (writer.good()) {
        std::cout << "Data file " << filename
                  << " written successfully!" << std::endl;
    } else {
        std::cout << "Failed to write data file " << filename
                  << "." << std::endl;
    }

    delete[] results;
}


////////////////////////////////////////////////////////////////////////////////


int main() {

    write_data_file<certificate_complexity<1>, 1>("CertificateComplexity");
    write_data_file<certificate_complexity<2>, 2>("CertificateComplexity");
    write_data_file<certificate_complexity<3>, 3>("CertificateComplexity");
    write_data_file<certificate_complexity<4>, 4>("CertificateComplexity");

    write_data_file<sensitivity<1>, 1>("Sensitivity");
    write_data_file<sensitivity<2>, 2>("Sensitivity");
    write_data_file<sensitivity<3>, 3>("Sensitivity");
    write_data_file<sensitivity<4>, 4>("Sensitivity");

    write_data_file<block_sensitivity<1>, 1>("BlockSensitivity");
    write_data_file<block_sensitivity<2>, 2>("BlockSensitivity");
    write_data_file<block_sensitivity<3>, 3>("BlockSensitivity");
    write_data_file<block_sensitivity<4>, 4>("BlockSensitivity");

    // std::uint8_t *const results = new std::uint8_t[NUM_FUNCS];
    // double completed = 0.0;

    // #pragma omp parallel for
    // for (std::uint64_t f = 0; f < NUM_FUNCS; ++f) {
    //     results[f] = static_cast<std::uint8_t>(
    //         block_sensitivity<N>(BooleanFunction{f})
    //     );
    //     if (f > 0 && f % INCREMENT == 0) {
    //         #pragma omp critical
    //         {
    //             completed += INCREMENT;
    //             std::printf("%02d : %10llu (%06.3f%%)\n",
    //                         omp_get_thread_num(), f,
    //                         100.0 * completed / NUM_FUNCS);
    //         }
    //     }
    // }

    // std::cout << "Counting number of occurrences..." << std::endl;
    // std::map<std::uint8_t, std::uint64_t> counts{};
    // for (std::uint64_t f = 0; f < NUM_FUNCS; ++f) {
    //     ++counts[results[f]];
    // }
    // for (const auto p : counts) {
    //     std::cout << static_cast<int>(p.first) << " : "
    //             << p.second << std::endl;
    // }

}
