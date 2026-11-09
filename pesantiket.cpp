#include <algorithm>
#include <climits>
#include <iomanip>
#include <iostream>
#include <map>
#include <queue>
#include <sstream>
#include <string>
#include <vector>

using namespace std;


struct Flight {
    string kode;       // kode penerbangan
    string maskapai;
    string asal;       // kode kota asal (mis. PKU)
    string tujuan;     // kode kota tujuan
    int berangkat;     // menit sejak 00:00
    int durasi;        // menit
    long harga;        // rupiah
};

string jam(int menit) {
    menit %= 24 * 60;
    ostringstream os;
    os << setfill('0') << setw(2) << menit / 60 << ":" << setw(2) << menit % 60;
    return os.str();
}

string rupiah(long v) {
    string s = to_string(v), out;
    int c = 0;
    for (int i = (int)s.size() - 1; i >= 0; --i) {
        out = s[i] + out;
        if (++c % 3 == 0 && i != 0) out = "." + out;
    }
    return "Rp" + out;
}

void cetakHeader() {
    cout << left << setw(8) << "Kode" << setw(14) << "Maskapai" << setw(6) << "Asal"
            << setw(8) << "Tujuan" << setw(11) << "Berangkat" << setw(8) << "Durasi"
            << "Harga\n"
            << string(66, '-') << "\n";
}

void cetakFlight(const Flight& f) {
    cout << left << setw(8) << f.kode << setw(14) << f.maskapai << setw(6) << f.asal
            << setw(8) << f.tujuan << setw(11) << jam(f.berangkat)
            << setw(8) << (to_string(f.durasi) + "m") << rupiah(f.harga) << "\n";
}

void cetakDaftar(const vector<Flight>& v) {
    if (v.empty()) {
        cout << "Tidak ada tiket yang ditemukan.\n";
        return;
    }
    cetakHeader();
    for (const auto& f : v) cetakFlight(f);
}

// ------------------------- SORTING --------------------------
// Merge Sort generik: stabil, O(n log n). Pembanding berupa fungsi.
template <typename Cmp>
void mergeSort(vector<Flight>& a, int l, int r, Cmp lebihKecil) {
    if (l >= r) return;
    int m = (l + r) / 2;
    mergeSort(a, l, m, lebihKecil);
    mergeSort(a, m + 1, r, lebihKecil);

    vector<Flight> tmp;
    tmp.reserve(r - l + 1);
    int i = l, j = m + 1;
    while (i <= m && j <= r) {
        if (!lebihKecil(a[j], a[i])) tmp.push_back(a[i++]);  // jaga stabilitas
        else tmp.push_back(a[j++]);
    }
    while (i <= m) tmp.push_back(a[i++]);
    while (j <= r) tmp.push_back(a[j++]);
    for (int k = 0; k < (int)tmp.size(); ++k) a[l + k] = tmp[k];
}

void urutkan(vector<Flight>& a, int kriteria) {
    if (a.empty()) return;
    int n = (int)a.size() - 1;
    switch (kriteria) {
        case 1: mergeSort(a, 0, n, [](const Flight& x, const Flight& y) { return x.harga < y.harga; }); break;
        case 2: mergeSort(a, 0, n, [](const Flight& x, const Flight& y) { return x.berangkat < y.berangkat; }); break;
        case 3: mergeSort(a, 0, n, [](const Flight& x, const Flight& y) { return x.durasi < y.durasi; }); break;
    }
}

// ------------------------ SEARCHING -------------------------
string upper(string s) {
    transform(s.begin(), s.end(), s.begin(), ::toupper);
    return s;
}

// Linear Search: cari semua tiket dengan asal & tujuan tertentu. O(n)
vector<Flight> cariRute(const vector<Flight>& data, const string& asal, const string& tujuan) {
    vector<Flight> hasil;
    for (const auto& f : data)
        if (f.asal == asal && f.tujuan == tujuan) hasil.push_back(f);
    return hasil;
}

// Binary Search: cari tiket berdasarkan kode penerbangan.
// Syarat: data harus terurut berdasarkan kode. O(log n)
int binarySearchKode(const vector<Flight>& terurut, const string& kode) {
    int lo = 0, hi = (int)terurut.size() - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (terurut[mid].kode == kode) return mid;
        if (terurut[mid].kode < kode) lo = mid + 1;
        else hi = mid - 1;
    }
    return -1;
}

// -------------------------- GRAPH ---------------------------
// Node = kota, Edge = penerbangan (berarah, berbobot harga)
class JaringanRute {
public:
    struct Edge { int ke; long biaya; int idx; };  // idx = indeks flight di data

    void bangun(const vector<Flight>& data) {
        kota.clear(); id.clear(); adj.clear();
        for (const auto& f : data) { ambilId(f.asal); ambilId(f.tujuan); }
        adj.assign(kota.size(), {});
        for (int i = 0; i < (int)data.size(); ++i)
            adj[id[data[i].asal]].push_back({id[data[i].tujuan], data[i].harga, i});
    }

    bool ada(const string& k) const { return id.count(k) > 0; }

    // Dijkstra: rute dengan biaya total minimum. O((V+E) log V)
    // Mengembalikan daftar indeks penerbangan yang dilalui, total biaya lewat parameter.
    vector<int> termurah(const string& asal, const string& tujuan, long& total) const {
        int n = (int)kota.size(), s = id.at(asal), t = id.at(tujuan);
        vector<long> dist(n, LLONG_MAX);
        vector<int> prevNode(n, -1), prevFlight(n, -1);
        priority_queue<pair<long, int>, vector<pair<long, int>>, greater<>> pq;
        dist[s] = 0;
        pq.push({0, s});
        while (!pq.empty()) {
            auto [d, u] = pq.top(); pq.pop();
            if (d > dist[u]) continue;
            for (const auto& e : adj[u]) {
                if (dist[u] + e.biaya < dist[e.ke]) {
                    dist[e.ke] = dist[u] + e.biaya;
                    prevNode[e.ke] = u;
                    prevFlight[e.ke] = e.idx;
                    pq.push({dist[e.ke], e.ke});
                }
            }
        }
        total = dist[t];
        vector<int> jalur;
        if (dist[t] == LLONG_MAX) return jalur;
        for (int v = t; v != s; v = prevNode[v]) jalur.push_back(prevFlight[v]);
        reverse(jalur.begin(), jalur.end());
        return jalur;
    }

    // BFS: rute dengan jumlah transit paling sedikit. O(V+E)
    vector<int> transitTerkecil(const string& asal, const string& tujuan) const {
        int n = (int)kota.size(), s = id.at(asal), t = id.at(tujuan);
        vector<int> prevNode(n, -1), prevFlight(n, -1);
        vector<bool> vis(n, false);
        queue<int> q;
        q.push(s); vis[s] = true;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (const auto& e : adj[u]) {
                if (!vis[e.ke]) {
                    vis[e.ke] = true;
                    prevNode[e.ke] = u;
                    prevFlight[e.ke] = e.idx;
                    q.push(e.ke);
                }
            }
        }
        vector<int> jalur;
        if (!vis[t]) return jalur;
        for (int v = t; v != s; v = prevNode[v]) jalur.push_back(prevFlight[v]);
        reverse(jalur.begin(), jalur.end());
        return jalur;
    }

    void tampilkan() const {
        cout << "\nJaringan rute (kota -> tujuan langsung):\n";
        for (int u = 0; u < (int)kota.size(); ++u) {
            cout << "  " << kota[u] << " -> ";
            vector<string> tujuan;
            for (const auto& e : adj[u]) {
                string nama = kota[e.ke];
                if (find(tujuan.begin(), tujuan.end(), nama) == tujuan.end()) tujuan.push_back(nama);
            }
            for (size_t i = 0; i < tujuan.size(); ++i) cout << tujuan[i] << (i + 1 < tujuan.size() ? ", " : "");
            cout << "\n";
        }
    }

private:
    vector<string> kota;
    map<string, int> id;
    vector<vector<Edge>> adj;

    int ambilId(const string& k) {
        auto it = id.find(k);
        if (it != id.end()) return it->second;
        id[k] = (int)kota.size();
        kota.push_back(k);
        return id[k];
    }
};

// ----------------------- DATA CONTOH ------------------------
vector<Flight> buatData() {
    auto M = [](int h, int m) { return h * 60 + m; };
    return {
        {"GA101", "Garuda",     "PKU", "CGK", M(6, 0),  100, 1250000},
        {"JT202", "Lion Air",   "PKU", "CGK", M(9, 30), 105,  890000},
        {"QG303", "Citilink",   "PKU", "CGK", M(14, 15), 100, 780000},
        {"ID404", "Batik Air",  "PKU", "KNO", M(7, 45),  75,  850000},
        {"JT505", "Lion Air",   "PKU", "BTH", M(11, 0),  60,  620000},
        {"GA606", "Garuda",     "CGK", "DPS", M(8, 0),  165, 1450000},
        {"QG707", "Citilink",   "CGK", "DPS", M(13, 20), 165, 1050000},
        {"JT808", "Lion Air",   "CGK", "SUB", M(10, 10), 100,  720000},
        {"GA909", "Garuda",     "CGK", "UPG", M(6, 50), 150, 1600000},
        {"ID110", "Batik Air",  "KNO", "CGK", M(12, 30), 150,  980000},
        {"JT211", "Lion Air",   "KNO", "BTH", M(15, 0),   90,  700000},
        {"QG312", "Citilink",   "BTH", "CGK", M(16, 40), 110,  760000},
        {"JT413", "Lion Air",   "BTH", "SUB", M(7, 15), 135,  950000},
        {"GA514", "Garuda",     "SUB", "DPS", M(9, 0),   65,  650000},
        {"QG615", "Citilink",   "SUB", "UPG", M(11, 45), 105,  870000},
        {"JT716", "Lion Air",   "UPG", "DPS", M(17, 30), 100,  830000},
        {"ID817", "Batik Air",  "DPS", "UPG", M(8, 20), 100,  900000},
        {"GA918", "Garuda",     "DPS", "CGK", M(19, 0), 170, 1300000},
    };
}

// ---------------------- ANTARMUKA MENU ----------------------
void tampilkanJalur(const vector<Flight>& data, const vector<int>& jalur) {
    cetakHeader();
    long total = 0;
    int durasi = 0;
    for (int i : jalur) { cetakFlight(data[i]); total += data[i].harga; durasi += data[i].durasi; }
    cout << string(66, '-') << "\n";
    cout << "Jumlah transit : " << (jalur.empty() ? 0 : (int)jalur.size() - 1) << "\n";
    cout << "Total biaya    : " << rupiah(total) << "\n";
    cout << "Total terbang  : " << durasi << " menit (belum termasuk waktu tunggu)\n";
}

string bacaKota(const string& label) {
    string s;
    cout << label;
    cin >> s;
    return upper(s);
}

int main() {
    vector<Flight> data = buatData();
    JaringanRute jaringan;
    jaringan.bangun(data);

    int pilih;
    do {
        cout << "\n===== SISTEM PEMESANAN TIKET PESAWAT =====\n"
                << "1. Tampilkan semua tiket\n"
                << "2. Urutkan tiket (harga / waktu berangkat / durasi)\n"
                << "3. Cari tiket langsung (kota asal & tujuan)\n"
                << "4. Cari tiket berdasarkan kode penerbangan (Binary Search)\n"
                << "5. Cari rute termurah (Graph - Dijkstra)\n"
                << "6. Cari rute transit paling sedikit (Graph - BFS)\n"
                << "7. Tampilkan jaringan rute\n"
                << "0. Keluar\n"
                << "Pilih menu: ";
        if (!(cin >> pilih)) break;

        if (pilih == 1) {
            cetakDaftar(data);
        } else if (pilih == 2) {
            int k;
            cout << "Urutkan berdasarkan: 1) Harga  2) Waktu berangkat  3) Durasi : ";
            cin >> k;
            if (k < 1 || k > 3) { cout << "Pilihan tidak valid.\n"; continue; }
            vector<Flight> salinan = data;
            urutkan(salinan, k);
            cetakDaftar(salinan);
        } else if (pilih == 3) {
            string a = bacaKota("Kota asal (mis. PKU)   : ");
            string t = bacaKota("Kota tujuan (mis. CGK) : ");
            vector<Flight> hasil = cariRute(data, a, t);
            urutkan(hasil, 1);  // tampilkan dari yang termurah
            cout << "\nTiket langsung " << a << " -> " << t << " (termurah dahulu):\n";
            cetakDaftar(hasil);
        } else if (pilih == 4) {
            string kode;
            cout << "Kode penerbangan (mis. GA101): ";
            cin >> kode;
            kode = upper(kode);
            vector<Flight> terurut = data;  // binary search butuh data terurut menurut kode
            mergeSort(terurut, 0, (int)terurut.size() - 1,
                        [](const Flight& x, const Flight& y) { return x.kode < y.kode; });
            int idx = binarySearchKode(terurut, kode);
            if (idx < 0) cout << "Kode " << kode << " tidak ditemukan.\n";
            else { cetakHeader(); cetakFlight(terurut[idx]); }
        } else if (pilih == 5 || pilih == 6) {
            string a = bacaKota("Kota asal   : ");
            string t = bacaKota("Kota tujuan : ");
            if (!jaringan.ada(a) || !jaringan.ada(t)) { cout << "Kota tidak dikenal.\n"; continue; }
            if (a == t) { cout << "Kota asal dan tujuan sama.\n"; continue; }
            vector<int> jalur;
            if (pilih == 5) {
                long total;
                jalur = jaringan.termurah(a, t, total);
                cout << "\nRute termurah " << a << " -> " << t << ":\n";
            } else {
                jalur = jaringan.transitTerkecil(a, t);
                cout << "\nRute transit paling sedikit " << a << " -> " << t << ":\n";
            }
            if (jalur.empty()) cout << "Tidak ada rute yang menghubungkan kedua kota.\n";
            else tampilkanJalur(data, jalur);
        } else if (pilih == 7) {
            jaringan.tampilkan();
        } else if (pilih != 0) {
            cout << "Menu tidak valid.\n";
        }
    } while (pilih != 0);

    cout << "Terima kasih.\n";
    return 0;
}
