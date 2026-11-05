#!/usr/bin/env node
// Chronoguesser: photos.json ビルドスクリプト
// Wikimedia Commons を検索して、撮影日が日単位で確かな街並み写真を集め、photos.json に書き出します。
// 使い方:  node scripts/build-photos.mjs          （Node.js 18 以上）
// 環境変数: PAGES_PER_QUERY（1クエリあたりの取得ページ数, 既定 4）
//           MAX_PER_DECADE（都市指定以外の写真の年代ごとの上限, 既定 250）
//           MAX_PER_CITY（都市ごとの上限, 既定 200）
//           OUTPUT（出力先, 既定 photos.json）

import { writeFileSync } from 'node:fs';

const API_ENDPOINT = 'https://commons.wikimedia.org/w/api.php';
const USER_AGENT = 'Chronoguesser-photo-builder/1.0 (https://wamo2351.github.io/chronoguesser; wamo.pjt.2351@gmail.com)';
const MIN_YEAR = 1850;
const MAX_YEAR = new Date().getFullYear();
const PAGES_PER_QUERY = Number(process.env.PAGES_PER_QUERY || 4);
const MAX_PER_DECADE = Number(process.env.MAX_PER_DECADE || 250);
const MAX_PER_CITY = Number(process.env.MAX_PER_CITY || 200);
const OUTPUT = process.env.OUTPUT || 'photos.json';
const MIN_PHOTOS_TO_WRITE = 200;     // これ未満なら失敗とみなし、既存ファイルを上書きしない
const REQUEST_INTERVAL_MS = Number(process.env.REQUEST_INTERVAL_MS || 1000);    // リクエストは1秒に1回まで（順番に1本ずつ）。下げないでください
const MONTH_NAMES_EN = { january: 1, february: 2, march: 3, april: 4, may: 5, june: 6, july: 7, august: 8, september: 9, october: 10, november: 11, december: 12 };

const sleep = ms => new Promise(r => setTimeout(r, ms));
function stripHtml(s) {
    return String(s || '').replace(/<[^>]*>/g, ' ').replace(/&nbsp;/g, ' ').replace(/&amp;/g, '&').replace(/&quot;/g, '"').replace(/&#039;/g, "'").replace(/\s+/g, ' ').trim();
}
function daysInMonth(year, month) {
    return new Date(year, month, 0).getDate();
}

// ===== ここから index.html（旧版）から移した出題条件 =====
function parseExactDate(rawHtml) {
    const raw = String(rawHtml || '');
    if (!raw) return null;
    if (/(circa|\bca\.|\bc\.\s?\d|between|before|after|unknown|decade|exif|\d{4}s\b|\bor\b|\?|P1480|P1319|P1326)/i.test(raw)) return null;
    const text = stripHtml(raw);
    let y, m, d, mm;
    mm = raw.match(/\+(\d{4})-(\d{2})-(\d{2})T[\d:]+Z\/11/);
    if (mm) { y = +mm[1]; m = +mm[2]; d = +mm[3]; }
    if (!y) { mm = text.match(/\b(\d{4})-(\d{2})-(\d{2})\b/); if (mm) { y = +mm[1]; m = +mm[2]; d = +mm[3]; } }
    if (!y) {
        mm = text.match(/\b(\d{1,2}) (January|February|March|April|May|June|July|August|September|October|November|December) (\d{4})\b/i);
        if (mm) { y = +mm[3]; m = MONTH_NAMES_EN[mm[2].toLowerCase()]; d = +mm[1]; }
    }
    if (!y) {
        mm = text.match(/\b(January|February|March|April|May|June|July|August|September|October|November|December) (\d{1,2}), (\d{4})\b/i);
        if (mm) { y = +mm[3]; m = MONTH_NAMES_EN[mm[1].toLowerCase()]; d = +mm[2]; }
    }
    if (!y || !m || !d) return null;
    if (m === 1 && d === 1) return null;
    if (m < 1 || m > 12 || d < 1 || d > daysInMonth(y, m)) return null;
    return { year: y, month: m, day: d };
}

const STREET_RE = /(street|straat|stra(ss|ß)e|\brue\b|avenue|boulevard|plein\b|platz|square|piazza|plaza|market|markt|tram|traffic|verkeer|verkehr|crossing|kruispunt|intersection|downtown|binnenstad|innenstadt|stadtansicht|stadsgezicht|straatbeeld|cityscape|townscape|shopping|winkel|gracht|kade\b|brücke|bridge|\bbrug\b|\bweg\b|road|allee|lane\b|drukte|looking (north|south|east|west))/i;
const BAD_RE = /(report|\bmap\b|kaart|karte|\bplan\b|drawing|tekening|poster|affiche|document|letter|stamp|logo|portrait|portret|porträt|interieur|interior|office|kantoor|employees|stolperstein|plaque|gedenktafel|cover|diagram|gedoopt|schip|\bship\b|vergadering|meeting|receptie|ontvangst|uitreiking|huldiging|award|zitting|sitzung|konferenz)/i;

const COLLECTIONS = [
    {
        id: 'anefo', name: 'Nationaal Archief / Anefo', country: 'オランダ', weight: 3, enabled: true, minYear: 1940, maxYear: 1989,
        terms: ['straatbeeld', 'verkeer', 'straat', 'winkelstraat', 'markt', 'tram', 'plein', 'gracht', 'Kalverstraat', 'Damrak', 'Leidseplein', 'Coolsingel', 'binnenstad', 'drukte', 'stadsgezichten'],
        query: t => `filetype:bitmap Bestanddeelnr ${t}`,
        locate: (title, desc) => {
            const m = desc.match(/Locatie\s*:\s*(.+?)\s+(Trefwoorden|Fotograaf|Persoonsnaam|Instellingsnaam|Auteursrechthebbende|Copyright)\s*:/i);
            return m ? `オランダ・${m[1]}` : 'オランダ';
        },
        describe: desc => {
            const m = desc.match(/Beschrijving\s*:\s*(.+?)\s+Datum\s*:/i);
            return m ? m[1] : desc;
        }
    },
    {
        id: 'bundesarchiv', name: 'Bundesarchiv (ドイツ連邦公文書館)', country: 'ドイツ', weight: 3, enabled: true, minYear: 1880, maxYear: 1991,
        terms: ['Straßenszene', 'Straße', 'Straßenbahn', 'Verkehr', 'Marktplatz', 'Stadtansicht', 'Alexanderplatz', 'Unter den Linden', 'Friedrichstraße', 'Leipzig Straße', 'Dresden Straße', 'Platz'],
        query: t => `filetype:bitmap "Bundesarchiv Bild" ${t}`,
        locate: title => {
            const parts = title.replace(/^File:/, '').split(',').map(s => s.trim());
            return parts.length > 1 ? `ドイツ・${parts[1]}` : 'ドイツ';
        },
        describe: desc => desc
            .replace(/For documentary purposes the German Federal Archive.*?politically extreme\s*\.?/i, '')
            .trim()
    },
    {
        id: 'seattle', name: 'Seattle Municipal Archives', country: 'アメリカ', weight: 2, enabled: true, minYear: 1890, maxYear: 1995,
        terms: ['street', 'avenue', 'traffic', 'intersection', 'looking north', 'looking south', 'boulevard'],
        query: t => `filetype:bitmap "Seattle Municipal Archives" ${t}`,
        locate: () => 'アメリカ・シアトル',
        describe: desc => desc
    },
    {
        id: 'toronto', name: 'City of Toronto Archives', country: 'カナダ', weight: 2, enabled: true, minYear: 1860, maxYear: 1995,
        terms: ['street', 'avenue', 'looking north', 'looking south', 'looking east', 'looking west', 'Yonge', 'Queen Street'],
        query: t => `filetype:bitmap "City of Toronto Archives" ${t}`,
        locate: () => 'カナダ・トロント',
        describe: desc => desc
    },
    {
        id: 'vancouver', name: 'City of Vancouver Archives', country: 'カナダ', weight: 1, enabled: true, minYear: 1880, maxYear: 1985,
        terms: ['street', 'avenue', 'Granville', 'Hastings'],
        query: t => `filetype:bitmap "City of Vancouver Archives" ${t}`,
        locate: () => 'カナダ・バンクーバー',
        describe: desc => desc
    },
    {
        id: 'boston', name: 'Boston Public Library (DPLA)', country: 'アメリカ', weight: 1, enabled: true, minYear: 1860, maxYear: 1980,
        terms: ['street', 'square', 'avenue'],
        query: t => `filetype:bitmap "Boston Public Library" ${t}`,
        locate: () => 'アメリカ・ボストン周辺',
        describe: desc => desc
    },
    {
        id: 'geograph', name: 'Geograph Britain and Ireland', country: 'イギリス・アイルランド', weight: 3, enabled: true, minYear: 1970, maxYear: 9999,
        terms: ['High Street', 'street', 'road', 'Market Place', 'square', 'lane', 'avenue', 'junction', 'town centre', 'shopping', 'bridge'],
        query: t => `filetype:bitmap "geograph.org.uk" ${t}`,
        locate: (title, desc, categories) => {
            const clean = title.replace(/^File:/i, '').replace(/\.[^.]+$/, '').replace(/\s*-\s*geograph\.org\.uk.*$/i, '');
            const parts = clean.split(',').map(s => s.trim()).filter(Boolean);
            if (parts.length > 1) return `イギリス / アイルランド・${parts.slice(1).join(' ')}`;
            return extractLocationFromMetadata(title, desc, categories) || 'イギリス・アイルランド';
        },
        describe: desc => desc
    },
    {
        id: 'panoramio', name: 'Panoramio Street Archive', country: '世界各国', weight: 3, enabled: true, minYear: 2000, maxYear: 2017,
        terms: ['street', 'avenue', 'boulevard', 'plaza', 'square', 'downtown', 'intersection', 'traffic', 'tram', 'cityscape', 'road'],
        query: t => `filetype:bitmap "panoramio" ${t}`,
        locate: (title, desc, categories) => {
            return extractLocationFromMetadata(title, desc, categories) || '不明';
        },
        describe: desc => desc
    },
    {
        id: 'kartaview', name: 'KartaView (OpenStreetCam)', country: '世界各国', weight: 3, enabled: true, minYear: 2014, maxYear: 9999,
        terms: ['street'],
        query: () => '',
        locate: () => '不明',
        describe: desc => desc
    }
];

const KNOWN_PLACES = [
    [/\b(Tokyo|Shinjuku|Shibuya|Ginza|Asakusa|Akihabara|Ueno|Ikebukuro|Chiyoda|Minato-ku|東京|新宿|渋谷|銀座|浅草)\b/i, '日本・東京'],
    [/\b(Osaka|Umeda|Namba|Shinsaibashi|Dotonbori|大阪|梅田|難波)\b/i, '日本・大阪'],
    [/\b(Kyoto|Gion|Kawaramachi|京都)\b/i, '日本・京都'],
    [/\b(Yokohama|横浜)\b/i, '日本・横浜'],
    [/\b(Nagoya|名古屋)\b/i, '日本・名古屋'],
    [/\b(Fukuoka|Hakata|Tenjin|福岡|博多)\b/i, '日本・福岡'],
    [/\b(Sapporo|札幌)\b/i, '日本・札幌'],
    [/\b(Japan|日本)\b/i, '日本'],
    [/\b(London|Westminster|Camden|Kensington|Chelsea|Soho|Piccadilly|Oxford Street|Regent Street)\b/i, 'イギリス・ロンドン'],
    [/\b(Manchester|Salford)\b/i, 'イギリス・マンチェスター'],
    [/\b(Edinburgh)\b/i, 'イギリス・エディンバラ'],
    [/\b(Glasgow)\b/i, 'イギリス・グラスゴー'],
    [/\b(Birmingham)\b/i, 'イギリス・バーミンガム'],
    [/\b(Liverpool)\b/i, 'イギリス・リヴァプール'],
    [/\b(Dublin)\b/i, 'アイルランド・ダブリン'],
    [/\b(Paris|Montmartre|Champs-Élysées|Champs-Elysees)\b/i, 'フランス・パリ'],
    [/\b(Lyon)\b/i, 'フランス・リヨン'],
    [/\b(Marseille)\b/i, 'フランス・マルセイユ'],
    [/\b(France)\b/i, 'フランス'],
    [/\b(Berlin|Kreuzberg|Charlottenburg|Mitte|Alexanderplatz|Kurfürstendamm)\b/i, 'ドイツ・ベルリン'],
    [/\b(Munich|München)\b/i, 'ドイツ・ミュンヘン'],
    [/\b(Hamburg)\b/i, 'ドイツ・ハンブルク'],
    [/\b(Frankfurt)\b/i, 'ドイツ・フランクフルト'],
    [/\b(Leipzig)\b/i, 'ドイツ・ライプツィヒ'],
    [/\b(Dresden)\b/i, 'ドイツ・ドレスデン'],
    [/\b(Cologne|Köln)\b/i, 'ドイツ・ケルン'],
    [/\b(Germany|Deutschland)\b/i, 'ドイツ'],
    [/\b(Amsterdam)\b/i, 'オランダ・アムステルダム'],
    [/\b(Rotterdam)\b/i, 'オランダ・ロッテルダム'],
    [/\b(The Hague|Den Haag|'s-Gravenhage)\b/i, 'オランダ・ハーグ'],
    [/\b(Utrecht)\b/i, 'オランダ・ユトレヒト'],
    [/\b(Netherlands|Nederland)\b/i, 'オランダ'],
    [/\b(New York|Manhattan|Brooklyn|Queens|Bronx|Broadway)\b/i, 'アメリカ・ニューヨーク'],
    [/\b(San Francisco)\b/i, 'アメリカ・サンフランシスコ'],
    [/\b(Los Angeles|Hollywood)\b/i, 'アメリカ・ロサンゼルス'],
    [/\b(Chicago)\b/i, 'アメリカ・シカゴ'],
    [/\b(Seattle)\b/i, 'アメリカ・シアトル'],
    [/\b(Boston)\b/i, 'アメリカ・ボストン'],
    [/\b(Washington,?\s*D\.?C\.?)\b/i, 'アメリカ・ワシントンD.C.'],
    [/\b(United States|USA)\b/i, 'アメリカ'],
    [/\b(Toronto)\b/i, 'カナダ・トロント'],
    [/\b(Vancouver)\b/i, 'カナダ・バンクーバー'],
    [/\b(Montreal|Montréal)\b/i, 'カナダ・モントリオール'],
    [/\b(Canada)\b/i, 'カナダ'],
    [/\b(Rome|Roma)\b/i, 'イタリア・ローマ'],
    [/\b(Milan|Milano)\b/i, 'イタリア・ミラノ'],
    [/\b(Venice|Venezia)\b/i, 'イタリア・ヴェネツィア'],
    [/\b(Florence|Firenze)\b/i, 'イタリア・フィレンツェ'],
    [/\b(Italy|Italia)\b/i, 'イタリア'],
    [/\b(Madrid)\b/i, 'スペイン・マドリード'],
    [/\b(Barcelona)\b/i, 'スペイン・バルセロナ'],
    [/\b(Spain|España)\b/i, 'スペイン'],
    [/\b(Vienna|Wien)\b/i, 'オーストリア・ウィーン'],
    [/\b(Prague|Praha)\b/i, 'チェコ・プラハ'],
    [/\b(Budapest)\b/i, 'ハンガリー・ブダペスト'],
    [/\b(Warsaw|Warszawa)\b/i, 'ポーランド・ワルシャワ'],
    [/\b(Moscow|Москва)\b/i, 'ロシア・モスクワ'],
    [/\b(Istanbul|İstanbul)\b/i, 'トルコ・イスタンブール'],
    [/\b(Taipei|台北|臺北)\b/i, '台湾・台北'],
    [/\b(Taiwan|台湾|臺灣)\b/i, '台湾'],
    [/\b(Seoul|서울|ソウル)\b/i, '韓国・ソウル'],
    [/\b(Busan|부산)\b/i, '韓国・釜山'],
    [/\b(South Korea|Korea)\b/i, '韓国'],
    [/\b(Hong Kong|香港)\b/i, '香港'],
    [/\b(Singapore)\b/i, 'シンガポール'],
    [/\b(Bangkok)\b/i, 'タイ・バンコク'],
    [/\b(Sydney)\b/i, 'オーストラリア・シドニー'],
    [/\b(Melbourne)\b/i, 'オーストラリア・メルボルン'],
    [/\b(Australia)\b/i, 'オーストラリア'],
    [/\b(São Paulo|Sao Paulo)\b/i, 'ブラジル・サンパウロ'],
    [/\b(Rio de Janeiro)\b/i, 'ブラジル・リオデジャネイロ'],
    [/\b(Buenos Aires)\b/i, 'アルゼンチン・ブエノスアイレス'],
    [/\b(Mexico City|Ciudad de México)\b/i, 'メキシコ・メキシコシティ']
];

function extractLocationFromMetadata(title, desc, categories) {
    const combined = `${title || ''} ${desc || ''} ${categories || ''}`;
    for (const [re, label] of KNOWN_PLACES) {
        if (re.test(combined)) return label;
    }
    if (categories) {
        const cats = String(categories).split('|').map(s => s.trim());
        for (const c of cats) {
            if (/(panoramio|wikimedia|cc-by|self-published|taken on|pages with|media with|files|images|unidentified|unknown)/i.test(c)) continue;
            const m = c.match(/^(?:Streets|Roads|Avenues|Boulevards|Squares|Plazas|Views|Architecture|Buildings|Transport|Traffic|Trams|Cityscapes|Townscapes|Photographs)\s+(?:in|of)\s+(.+)$/i);
            if (m && m[1] && !/^\d+$/.test(m[1])) {
                return m[1].replace(/^the\s+/i, '').trim();
            }
        }
    }
    const cleanTitle = String(title || '')
        .replace(/^File:/i, '')
        .replace(/\.[^.]+$/, '')
        .replace(/\s*-\s*panoramio.*$/i, '')
        .replace(/\s*-\s*geograph\.org\.uk.*$/i, '')
        .trim();
    const parts = cleanTitle.split(',').map(s => s.trim()).filter(Boolean);
    if (parts.length >= 2) {
        const last = parts[parts.length - 1];
        if (last.length >= 2 && last.length <= 35 && !/^\d+$/.test(last) && !/^(street|road|avenue|view|photo|panoramio)$/i.test(last)) {
            return parts.slice(-2).join('・');
        }
    }
    return null;
}

const CITY_FILTERS = [
    { id: 'all', label: 'すべての都市', shortLabel: '全都市', preset: true },
    {
        id: 'tokyo', label: '東京', locationName: '日本・東京', preset: true,
        lat: 35.6812, lng: 139.7671,
        matchRe: /\b(Tokyo|Shinjuku|Shibuya|Ginza|Asakusa|Akihabara|Ueno|Ikebukuro|Harajuku|Roppongi|Shinagawa|Chiyoda|Chuo|Minato|Taito|東京|新宿|渋谷|銀座|浅草|秋葉原|上野|池袋)\b/i,
        queries: [
            'filetype:bitmap "Tokyo" (street OR road OR avenue OR crossing OR intersection OR Shibuya OR Shinjuku OR Ginza)',
            'filetype:bitmap "panoramio" Tokyo (street OR road OR Shinjuku OR Shibuya OR Ginza)'
        ]
    },
    {
        id: 'london', label: 'ロンドン', locationName: 'イギリス・ロンドン', preset: true,
        lat: 51.5074, lng: -0.1278,
        matchRe: /\b(London|Westminster|Camden|Kensington|Chelsea|Islington|Hackney|Southwark|Lambeth|Tower Hamlets|Greenwich|Soho|Piccadilly|Oxford Street|Regent Street|Strand|Whitehall|Fleet Street)\b/i,
        queries: [
            'filetype:bitmap "geograph.org.uk" London (Street OR Road OR Square OR Lane OR Avenue)',
            'filetype:bitmap "London" (street OR road OR square OR Piccadilly OR Strand OR Oxford Street)'
        ]
    },
    {
        id: 'paris', label: 'パリ', locationName: 'フランス・パリ', preset: true,
        lat: 48.8566, lng: 2.3522,
        matchRe: /\b(Paris|Montmartre|Champs-Élysées|Champs-Elysees|Rivoli|Haussmann|Saint-Germain|Bastille|Pigalle|Marais)\b/i,
        queries: [
            'filetype:bitmap "Paris" (rue OR avenue OR boulevard OR place OR street)',
            'filetype:bitmap "panoramio" Paris (rue OR avenue OR boulevard OR street)'
        ]
    },
    {
        id: 'berlin', label: 'ベルリン', locationName: 'ドイツ・ベルリン', preset: true,
        lat: 52.5200, lng: 13.4050,
        matchRe: /\b(Berlin|Alexanderplatz|Unter den Linden|Friedrichstraße|Friedrichstrasse|Kurfürstendamm|Potsdamer Platz|Kreuzberg|Charlottenburg|Prenzlauer Berg)\b/i,
        queries: [
            'filetype:bitmap "Bundesarchiv Bild" Berlin (Straße OR Platz OR Verkehr OR Straßenbahn OR Alexanderplatz OR Friedrichstraße)',
            'filetype:bitmap "Berlin" (Straße OR Platz OR Alexanderplatz OR Friedrichstraße OR Kurfürstendamm)'
        ]
    },
    {
        id: 'amsterdam', label: 'アムステルダム', locationName: 'オランダ・アムステルダム', preset: true,
        lat: 52.3676, lng: 4.9041,
        matchRe: /\b(Amsterdam|Amsterdamse|Damrak|Kalverstraat|Leidsestraat|Leidseplein|Rembrandtplein|Rokin|Vijzelstraat|Prinsengracht|Keizersgracht|Herengracht|Singel)\b/i,
        queries: [
            'filetype:bitmap Bestanddeelnr Amsterdam (straat OR plein OR gracht OR verkeer OR tram OR Damrak OR Kalverstraat)',
            'filetype:bitmap "Amsterdam" (straat OR gracht OR plein OR Damrak OR Kalverstraat)'
        ]
    },
    {
        id: 'newyork', label: 'ニューヨーク', locationName: 'アメリカ・ニューヨーク', preset: true,
        lat: 40.7580, lng: -73.9855,
        matchRe: /\b(New York|Manhattan|Brooklyn|Queens|Bronx|Broadway|Fifth Avenue|5th Avenue|Times Square|Wall Street|Harlem|SoHo|Chinatown)\b/i,
        queries: [
            'filetype:bitmap "New York" (street OR avenue OR Broadway OR Manhattan OR Brooklyn OR intersection)',
            'filetype:bitmap "panoramio" "New York" (street OR avenue OR Broadway OR Manhattan)'
        ]
    },
    {
        id: 'toronto', label: 'トロント', locationName: 'カナダ・トロント', preset: true,
        lat: 43.6532, lng: -79.3832,
        matchRe: /\b(Toronto|Yonge|Queen Street|King Street|Bloor|Dundas|Spadina|Front Street|Bay Street)\b/i,
        queries: [
            'filetype:bitmap "City of Toronto Archives" (street OR avenue OR Yonge OR Queen OR King)',
            'filetype:bitmap "Toronto" (street OR avenue OR Yonge OR Queen Street OR King Street)'
        ]
    },
    {
        id: 'seattle', label: 'シアトル', locationName: 'アメリカ・シアトル', preset: false,
        lat: 47.6062, lng: -122.3321,
        matchRe: /\b(Seattle|Rainier|Pike|Pine Street|Madison Street|Yesler|Alaskan Way|Ballard|Fremont|Capitol Hill)\b/i,
        queries: [
            'filetype:bitmap "Seattle Municipal Archives" (street OR avenue OR boulevard OR traffic OR intersection)',
            'filetype:bitmap "Seattle" (street OR avenue OR Pike OR Broadway OR downtown)'
        ]
    },
    {
        id: 'osaka', label: '大阪', locationName: '日本・大阪', preset: false,
        lat: 34.6937, lng: 135.5023,
        matchRe: /\b(Osaka|Umeda|Namba|Shinsaibashi|Dotonbori|Shinsekai|Tennoji|Midosuji|大阪|梅田|難波|心斎橋|道頓堀|御堂筋)\b/i,
        queries: [
            'filetype:bitmap "Osaka" (street OR road OR Umeda OR Namba OR Dotonbori OR Shinsaibashi)',
            'filetype:bitmap "panoramio" Osaka'
        ]
    },
    {
        id: 'manchester', label: 'マンチェスター', locationName: 'イギリス・マンチェスター', preset: false,
        lat: 53.4808, lng: -2.2426,
        matchRe: /\b(Manchester|Salford|Deansgate|Mosley Street|Market Street|Oxford Road|Piccadilly)\b/i,
        queries: [
            'filetype:bitmap "geograph.org.uk" Manchester (Street OR Road OR Square)',
            'filetype:bitmap "Manchester" (Street OR Road OR Square OR Deansgate)'
        ]
    },
    {
        id: 'rotterdam', label: 'ロッテルダム', locationName: 'オランダ・ロッテルダム', preset: false,
        lat: 51.9244, lng: 4.4777,
        matchRe: /\b(Rotterdam|Coolsingel|Lijnbaan|Hofplein|Blaak|Witte de Withstraat)\b/i,
        queries: [
            'filetype:bitmap Bestanddeelnr Rotterdam (straat OR plein OR Coolsingel OR verkeer OR tram)',
            'filetype:bitmap "Rotterdam" (straat OR plein OR Coolsingel)'
        ]
    },
    {
        id: 'sanfrancisco', label: 'サンフランシスコ', locationName: 'アメリカ・サンフランシスコ', preset: false,
        lat: 37.7749, lng: -122.4194,
        matchRe: /\b(San Francisco|Market Street|Mission Street|Geary|Powell Street|Lombard Street|Embarcadero)\b/i,
        queries: [
            'filetype:bitmap "San Francisco" (street OR avenue OR Market Street OR cable car OR intersection)',
            'filetype:bitmap "panoramio" "San Francisco" (street OR avenue)'
        ]
    },
    {
        id: 'boston', label: 'ボストン', locationName: 'アメリカ・ボストン', preset: false,
        lat: 42.3601, lng: -71.0589,
        matchRe: /\b(Boston|Boylston|Tremont|Beacon Street|Newbury Street|Commonwealth Avenue|Washington Street)\b/i,
        queries: [
            'filetype:bitmap "Boston Public Library" (street OR square OR avenue)',
            'filetype:bitmap "Boston" (street OR avenue OR Boylston OR Tremont OR Beacon Street)'
        ]
    },
    {
        id: 'vancouver', label: 'バンクーバー', locationName: 'カナダ・バンクーバー', preset: false,
        lat: 49.2827, lng: -123.1207,
        matchRe: /\b(Vancouver|Granville|Hastings|Robson Street|Burrard|Cambie|Gastown)\b/i,
        queries: [
            'filetype:bitmap "City of Vancouver Archives" (street OR avenue OR Granville OR Hastings)',
            'filetype:bitmap "Vancouver" (street OR avenue OR Granville OR Hastings OR Robson)'
        ]
    },
    {
        id: 'taipei', label: '台北', locationName: '台湾・台北', preset: false,
        lat: 25.0330, lng: 121.5654,
        matchRe: /\b(Taipei|Ximending|Zhongxiao|Nanjing East|Xinyi|台北|臺北)\b/i,
        queries: [
            'filetype:bitmap "Taipei" (street OR road OR boulevard OR intersection OR Ximending)',
            'filetype:bitmap "panoramio" Taipei'
        ]
    },
    {
        id: 'seoul', label: 'ソウル', locationName: '韓国・ソウル', preset: false,
        lat: 37.5665, lng: 126.9780,
        matchRe: /\b(Seoul|Gangnam|Myeongdong|Jongno|Itaewon|Hongdae|Insadong|서울|ソウル)\b/i,
        queries: [
            'filetype:bitmap "Seoul" (street OR road OR avenue OR Gangnam OR Myeongdong OR Jongno)',
            'filetype:bitmap "panoramio" Seoul'
        ]
    },
    {
        id: 'sydney', label: 'シドニー', locationName: 'オーストラリア・シドニー', preset: false,
        lat: -33.8688, lng: 151.2093,
        matchRe: /\b(Sydney|George Street|Pitt Street|Oxford Street|Parramatta Road|Circular Quay)\b/i,
        queries: [
            'filetype:bitmap "Sydney" (street OR road OR George Street OR Pitt Street OR Oxford Street)',
            'filetype:bitmap "panoramio" Sydney (street OR road)'
        ]
    }
];


const CURATED_STREETS = [
    {
        file: 'Front Street West, looking west from Yonge Street.jpg', date: [1872, 10, 26],
        title: 'トロント、ヤング通りから西を望むフロント・ストリート', location: 'カナダ・トロント',
        description: 'Canadian Illustrated News に掲載された19世紀後半のトロント中心部。ヴィクトリア朝の商業建築と馬車の時代の北米都市。',
        collection: 'City of Toronto Archives'
    },
    {
        file: 'Terauley Street looking south towards Queen Street 1913.jpg', date: [1913, 6, 10],
        title: 'テローリー通り（現ベイ・ストリート）からクイーン通り方面を望む', location: 'カナダ・トロント',
        description: 'アルバート通りから南を望む。左手は旧トロント市庁舎。路面電車・馬車・初期の自動車が混在する時代の街路。',
        collection: 'City of Toronto Archives'
    },
    {
        file: 'Seattle - Hill Street looking east from Rainier Avenue, 1914 (23635307395).jpg', date: [1914, 1, 23],
        title: 'シアトル、レーニア・アベニューから東を望むヒル・ストリート', location: 'アメリカ・シアトル',
        description: '冬のシアトル郊外の街路。左手前の住宅は100年後の2015年時点でも現存している。',
        collection: 'Seattle Municipal Archives'
    },
    {
        file: 'Merton Street Toronto 1918.jpg', date: [1918, 11, 3],
        title: 'トロント、マートン・ストリート', location: 'カナダ・トロント',
        description: '第一次世界大戦の休戦（1918年11月11日）直前、晩秋のトロントの住宅街。',
        collection: 'City of Toronto Archives'
    },
    {
        file: 'Yonge Street north at Charles Street.jpg', date: [1938, 10, 13],
        title: 'トロント、チャールズ通り交差点から北を望むヤング・ストリート', location: 'カナダ・トロント',
        description: 'トロントの目抜き通りヤング・ストリート。1930年代後半の自動車、路面電車、商店の看板が並ぶ。',
        collection: 'City of Toronto Archives'
    },
    {
        file: 'Seattle - Madison Street, 1941 (38175096175).jpg', date: [1941, 1, 7],
        title: 'シアトル、20番街から西を望むマディソン・ストリート', location: 'アメリカ・シアトル',
        description: '太平洋戦争開戦の約1年前、冬のシアトルの商業通り。',
        collection: 'Seattle Municipal Archives'
    },
    {
        file: 'Bundesarchiv Bild 183-14602-0018, Weimar, Marktplatz, Neptunbrunnen, Ruine.jpg', date: [1952, 5, 11],
        title: 'ヴァイマル、マルクト広場とネプチューンの泉、戦災の廃墟', location: 'ドイツ（旧東ドイツ）・ヴァイマル',
        description: '東ドイツの通信社 Zentralbild による報道写真。第二次世界大戦の爆撃で損壊した建物がまだ残るマルクト広場。',
        collection: 'Bundesarchiv'
    },
    {
        file: 'Bundesarchiv Bild 183-41100-0017, Leipzig, Marktplatz, "Altes Rathaus".jpg', date: [1956, 8, 31],
        title: 'ライプツィヒ、マルクト広場と旧市庁舎', location: 'ドイツ（旧東ドイツ）・ライプツィヒ',
        description: 'ライプツィヒ秋季見本市（Herbstmesse 1956）の時期に撮影された、ルネサンス様式の旧市庁舎とマルクト広場。',
        collection: 'Bundesarchiv'
    },
    {
        file: 'Koningsplein met verkeer (afsluiting Leidsestraat), Bestanddeelnr 911-5722.jpg', date: [1960, 9, 6],
        title: 'アムステルダム、コーニングス広場の交通（ライツェ通り閉鎖時）', location: 'オランダ・アムステルダム',
        description: 'ライツェ通りの閉鎖に伴い交通が集中したコーニングス広場。自転車・路面電車・自動車が入り混じる1960年代のアムステルダム。',
        collection: 'Nationaal Archief / Anefo'
    },
    {
        file: 'Seattle - E. Green Lake Way and Ravenna Boulevard, 1963.jpg', date: [1963, 1, 9],
        title: 'シアトル、E.グリーンレイク・ウェイとラヴェンナ大通り', location: 'アメリカ・シアトル',
        description: '手前がE.グリーンレイク・ウェイ。写っている自転車店は現在の Gregg\'s Greenlake Bicycles。',
        collection: 'Seattle Municipal Archives'
    },
    {
        file: 'Paasdrukte op Amsterdamse Damrak, Bestanddeelnr 919-0107.jpg', date: [1966, 4, 8],
        title: 'アムステルダム、ダムラック通りの復活祭（イースター）の賑わい', location: 'オランダ・アムステルダム',
        description: 'イースター休暇で混雑するアムステルダム中央駅前のダムラック通り。',
        collection: 'Nationaal Archief / Anefo'
    },
    {
        file: 'Onlusten in Amsterdam, overzicht Damrak, Bestanddeelnr 919-2512.jpg', date: [1966, 6, 14],
        title: 'アムステルダム、騒乱の日のダムラック通り俯瞰', location: 'オランダ・アムステルダム',
        description: '1966年6月、建設労働者の抗議をきっかけに起きたアムステルダムの騒乱の際のダムラック通り。',
        collection: 'Nationaal Archief / Anefo'
    },
    {
        file: 'Ramsay Street, Rochdale, Lancashire - geograph.org.uk - 566083.jpg', date: [1979, 9, 15],
        title: 'ロッチデール、ラムジー・ストリート', location: 'イギリス・ランカシャー州ロッチデール',
        description: 'バルワー通りとの交差点の東側。撮影当時すでに老朽化していた19世紀のテラスハウスが並ぶ。',
        collection: 'Geograph Britain and Ireland'
    },
    {
        file: 'Toeschouwers kijken naar het verkeer, Bestanddeelnr 932-7211.jpg', date: [1983, 10, 4],
        title: 'カンペン、新しいアイセル橋の開通日に交通を見物する人々', location: 'オランダ・オーファーアイセル州カンペン',
        description: 'アイセル川に架かる新橋の開通日。行き交う1980年代の自動車を見物する市民。',
        collection: 'Nationaal Archief / Anefo'
    },
    {
        file: 'Bundesarchiv Bild 183-1985-0902-003, Quedlinburg, Marktplatz, Rathaus.jpg', date: [1985, 9, 2],
        title: 'クヴェードリンブルク、マルクト広場と市庁舎', location: 'ドイツ（旧東ドイツ）・クヴェードリンブルク',
        description: '東ドイツ時代末期の古都クヴェードリンブルク。のちに世界遺産となる旧市街の広場。',
        collection: 'Bundesarchiv'
    },
    {
        file: "Mosley Street, towards St Peter's Square - geograph.org.uk - 692157.jpg", date: [1990, 5, 12],
        title: 'マンチェスター、セント・ピーターズ・スクエア方面を望むモズリー・ストリート', location: 'イギリス・マンチェスター',
        description: 'プリンセス・ストリートとの交差点から。メトロリンク（路面電車）開業直前のマンチェスター中心部。',
        collection: 'Geograph Britain and Ireland'
    }
];

// ===== ここまで =====

let lastRequestAt = 0;
let requestCount = 0;
async function api(params) {
    const qs = new URLSearchParams({ format: 'json', formatversion: '2', maxlag: '5', ...params });
    for (let attempt = 0; attempt < 6; attempt++) {
        const wait = lastRequestAt + REQUEST_INTERVAL_MS - Date.now();
        if (wait > 0) await sleep(wait);
        lastRequestAt = Date.now();
        requestCount++;
        let res;
        try {
            res = await fetch(`${API_ENDPOINT}?${qs}`, { headers: { 'User-Agent': USER_AGENT } });
        } catch (e) {
            console.warn(`  network error: ${e.message} — retry`);
            await sleep(5000 * (attempt + 1));
            continue;
        }
        if (res.status === 429 || res.status >= 500) {
            const retryAfter = Number(res.headers.get('retry-after')) || 10 * (attempt + 1);
            console.warn(`  HTTP ${res.status} — ${retryAfter}s 待って再試行`);
            await sleep(retryAfter * 1000);
            continue;
        }
        const data = await res.json();
        if (data?.error?.code === 'maxlag') {
            const retryAfter = Number(res.headers.get('retry-after')) || 5;
            await sleep(retryAfter * 1000);
            continue;
        }
        if (data?.error) throw new Error(`API error: ${data.error.code} ${data.error.info}`);
        return data;
    }
    throw new Error('API request failed after retries');
}

async function searchFiles(query, pages = PAGES_PER_QUERY) {
    const out = [];
    let cont = {};
    for (let i = 0; i < pages; i++) {
        const data = await api({
            action: 'query',
            generator: 'search', gsrsearch: query, gsrnamespace: '6', gsrlimit: '40',
            prop: 'imageinfo', iiprop: 'url|size|extmetadata', iiurlwidth: '1280',
            iiextmetadatafilter: 'DateTimeOriginal|ImageDescription|Artist|Categories|LicenseShortName',
            ...cont
        });
        out.push(...(data?.query?.pages || []));
        if (!data.continue) break;
        cont = data.continue;
    }
    return out;
}

function cleanTitle(title) {
    return title
        .replace(/^File:/i, '')
        .replace(/\.[^.]+$/, '')
        .replace(/,?\s*Bestanddeelnr\s*[\d-]+/i, '')
        .replace(/^Bundesarchiv Bild [\w-]+,\s*/i, '')
        .replace(/\s*-\s*DPLA\s*-\s*\w+$/i, '')
        .replace(/\s*-\s*geograph\.org\.uk\s*-\s*\d+$/i, '')
        .replace(/\s*-\s*panoramio(?:\s*\(\d+\))?$/i, '')
        .replace(/\s*\(\d{6,}\)\s*$/, '')
        .trim();
}

// 検索結果1件を出題データに変換（条件に合わなければ null）
function toRecord(p, src) {
    const ii = p.imageinfo?.[0];
    if (!ii || !ii.thumburl) return null;
    if (!/\.(jpe?g|png|tiff?)$/i.test(p.title)) return null;
    if (ii.width < 640 || ii.height < 400) return null;
    const ratio = ii.width / ii.height;
    if (ratio > 3 || ratio < 0.5) return null;

    const md = ii.extmetadata || {};
    const license = stripHtml(md.LicenseShortName?.value).slice(0, 60);
    if (!license) return null;
    const actual = parseExactDate(md.DateTimeOriginal?.value);
    if (!actual || actual.year < MIN_YEAR || actual.year > MAX_YEAR) return null;

    const desc = stripHtml(md.ImageDescription?.value);
    const cats = stripHtml(md.Categories?.value);
    if (BAD_RE.test(p.title)) return null;
    if (!STREET_RE.test(`${p.title} ${desc} ${src.city ? cats : ''}`)) return null;
    if (src.city && src.city.matchRe && !src.city.matchRe.test(`${p.title} ${desc} ${cats}`)) return null;

    const yearsInTitle = (p.title.match(/\b(18[4-9]\d|19\d\d|20\d\d)\b/g) || []).map(Number);
    if (yearsInTitle.length && !yearsInTitle.includes(actual.year)) return null;

    const location = src.city
        ? src.city.locationName
        : (src.col.locate(p.title, desc, cats) || '不明');
    const description = (src.col ? (src.col.describe(desc) || desc) : desc).slice(0, 240);

    return {
        id: `commons-${p.pageid}`,
        eventKey: `${location}|${actual.year}-${actual.month}-${actual.day}`,
        actual,
        title: cleanTitle(p.title),
        location,
        description: description || '（説明文なし）',
        imageUrl: ii.thumburl,
        sourceUrl: ii.descriptionurl || `https://commons.wikimedia.org/?curid=${p.pageid}`,
        collection: src.city ? `Wikimedia Commons (${src.city.label})` : src.col.name,
        credit: stripHtml(md.Artist?.value).slice(0, 80),
        license,
        _fromCity: Boolean(src.city)
    };
}

const byId = new Map();
const byEvent = new Set();
function addPages(pages, src) {
    let added = 0;
    for (const p of pages) {
        const id = `commons-${p.pageid}`;
        if (byId.has(id)) continue;
        const rec = toRecord(p, src);
        if (!rec || byEvent.has(rec.eventKey)) continue;   // 同じ場所・同じ日の連作は1枚だけ
        byId.set(id, rec);
        byEvent.add(rec.eventKey);
        added++;
    }
    return added;
}

async function collectCurated() {
    const titles = CURATED_STREETS.map(p => `File:${p.file}`);
    const result = [];
    for (let i = 0; i < titles.length; i += 50) {
        const batch = titles.slice(i, i + 50);
        const data = await api({
            action: 'query', titles: batch.join('|'),
            prop: 'imageinfo', iiprop: 'url|extmetadata', iiurlwidth: '1280',
            iiextmetadatafilter: 'Artist|LicenseShortName'
        });
        const norm = {};
        (data?.query?.normalized || []).forEach(n => { norm[n.from] = n.to; });
        const pages = {};
        (data?.query?.pages || []).forEach(pg => { if (pg && !pg.missing) pages[pg.title] = pg; });
        batch.forEach((title, j) => {
            const src = CURATED_STREETS[i + j];
            const pg = pages[norm[title] || title];
            const ii = pg?.imageinfo?.[0];
            const md = ii?.extmetadata || {};
            const license = stripHtml(md.LicenseShortName?.value).slice(0, 60);
            if (!ii || !ii.thumburl || !license) {
                console.warn(`  厳選写真を除外（ライセンス不明または見つからない）: ${src.file}`);
                return;
            }
            result.push({
                id: `curated-${src.file}`,
                eventKey: `${src.location}|${src.date.join('-')}`,
                actual: { year: src.date[0], month: src.date[1], day: src.date[2] },
                title: src.title,
                location: src.location,
                description: src.description,
                imageUrl: ii.thumburl,
                sourceUrl: ii.descriptionurl || `https://commons.wikimedia.org/wiki/File:${encodeURIComponent(src.file.replace(/ /g, '_'))}`,
                collection: src.collection,
                credit: stripHtml(md.Artist?.value).slice(0, 80),
                license,
                curated: true
            });
        });
    }
    return result;
}

function shuffle(arr) {
    const a = [...arr];
    for (let i = a.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
}

async function main() {
    const started = Date.now();

    console.log('== 厳選写真のメタデータ取得');
    const curated = await collectCurated();
    console.log(`  ${curated.length} / ${CURATED_STREETS.length} 枚`);

    // 都市指定の検索を先に行う（場所ラベルが正確になるため）
    for (const city of CITY_FILTERS) {
        if (!city.queries) continue;
        for (const q of city.queries) {
            const pages = await searchFiles(q);
            console.log(`[city:${city.id}] +${addPages(pages, { city })}  (${q})`);
        }
    }

    for (const col of COLLECTIONS) {
        if (!col.enabled || col.id === 'kartaview') continue;
        for (const term of col.terms) {
            const q = col.query(term);
            const pages = await searchFiles(q);
            console.log(`[${col.id}] +${addPages(pages, { col })}  (${q})`);
        }
        // 年代の絞り込みでも出題できるよう、5年刻みで年を付けた検索も行う
        const lo = Math.max(MIN_YEAR, col.minYear ?? MIN_YEAR);
        const hi = Math.min(MAX_YEAR, col.maxYear ?? MAX_YEAR);
        let k = 0;
        for (let y = Math.ceil(lo / 5) * 5; y <= hi; y += 5, k++) {
            const q = col.query(`${col.terms[k % col.terms.length]} ${y}`);
            const pages = await searchFiles(q, 1);
            console.log(`[${col.id}:${y}] +${addPages(pages, { col })}`);
        }
    }

    // 都市ごと・年代ごとに上限をかけて、ファイルサイズを抑える
    const all = [...byId.values()];
    const byCity = {};
    all.filter(p => p._fromCity).forEach(p => { (byCity[p.location] ||= []).push(p); });
    const cityPhotos = Object.values(byCity).flatMap(list => shuffle(list).slice(0, MAX_PER_CITY));
    const general = all.filter(p => !p._fromCity);
    const byDecade = {};
    general.forEach(p => { const d = Math.floor(p.actual.year / 10) * 10; (byDecade[d] ||= []).push(p); });
    const capped = Object.values(byDecade).flatMap(list => shuffle(list).slice(0, MAX_PER_DECADE));

    const curatedIds = new Set(curated.map(p => p.eventKey));
    const photos = [...curated, ...cityPhotos, ...capped]
        .filter((p, i, arr) => p.curated || !curatedIds.has(p.eventKey))
        .map(({ _fromCity, ...rest }) => rest)
        .sort((a, b) => a.id.localeCompare(b.id));

    // 集計
    const decadeCount = {};
    photos.forEach(p => { const d = Math.floor(p.actual.year / 10) * 10; decadeCount[d] = (decadeCount[d] || 0) + 1; });
    console.log('\n== 年代別');
    Object.keys(decadeCount).sort().forEach(d => console.log(`  ${d}s: ${decadeCount[d]}`));
    console.log('== 都市別（都市指定の検索分）');
    CITY_FILTERS.filter(c => c.locationName).forEach(c => {
        console.log(`  ${c.id}: ${photos.filter(p => p.location === c.locationName).length}`);
    });
    console.log(`\n合計 ${photos.length} 枚 / APIリクエスト ${requestCount} 回 / ${Math.round((Date.now() - started) / 1000)} 秒`);

    if (photos.length < MIN_PHOTOS_TO_WRITE) {
        console.error(`写真が ${photos.length} 枚しか集まらなかったため、${OUTPUT} は更新しません。`);
        process.exit(1);
    }
    const body = '{"generatedAt":' + JSON.stringify(new Date().toISOString()) +
        ',"count":' + photos.length + ',"photos":[\n' +
        photos.map(p => JSON.stringify(p)).join(',\n') + '\n]}\n';
    writeFileSync(OUTPUT, body);
    console.log(`${OUTPUT} を書き出しました（${Math.round(body.length / 1024)} KB）`);
}

main().catch(e => { console.error(e); process.exit(1); });
