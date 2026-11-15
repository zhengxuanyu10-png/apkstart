'use strict';
/**
 * 测试夹具生成器：从零手写一个合法的最小 APK（不含 aapt / Android SDK 依赖）。
 *
 * 产出结构：
 *   AndroidManifest.xml   真正的二进制 AXML（字符串池 + 命名空间 + 元素树）
 *   resources.arsc        真正的资源表（string / mipmap 两个 type，含全局字符串池）
 *   res/mipmap-xxxhdpi/ic_launcher.png
 *
 * 用途：让 test/run-tests.js 在没有真实 APK 的机器上也能完整跑
 *       zip → axml → arsc → apk 这条离线解析链，而不是直接跳过。
 *
 * 用法：
 *   const { buildSampleApk } = require('./fixtures/make-apk');
 *   const file = buildSampleApk(os.tmpdir());           // 返回 apk 路径
 * 或命令行：
 *   node test/fixtures/make-apk.js out/sample.apk
 */
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { encodePng } = require('../src/core/png');

const ANDROID_NS = 'http://schemas.android.com/apk/res/android';

/* ---------------------------------- 工具 ---------------------------------- */

function u16(v) { const b = Buffer.alloc(2); b.writeUInt16LE(v & 0xffff, 0); return b; }
function u32(v) { const b = Buffer.alloc(4); b.writeUInt32LE(v >>> 0, 0); return b; }
function pad4(n) { return (4 - (n % 4)) % 4; }

/** UTF-8 字符串池长度前缀：>0x7F 用两个字节，最高位做续延标记 */
function encLen(n) {
  if (n > 0x7f) return Buffer.from([0x80 | ((n >> 8) & 0x7f), n & 0xff]);
  return Buffer.from([n & 0x7f]);
}

/** ResStringPool（UTF-8 变体，flags=0x100） */
function stringPool(strings) {
  const chunks = [];
  const offsets = [];
  let cursor = 0;
  for (const s of strings) {
    const bytes = Buffer.from(s, 'utf8');
    const body = Buffer.concat([encLen(s.length), encLen(bytes.length), bytes, Buffer.from([0])]);
    offsets.push(cursor);
    chunks.push(body);
    cursor += body.length;
  }
  const blob = Buffer.concat(chunks);
  const headerSize = 28;
  const stringsStart = headerSize + strings.length * 4;
  const padding = pad4(stringsStart + blob.length);
  const size = stringsStart + blob.length + padding;
  return Buffer.concat([
    u16(0x0001), u16(headerSize), u32(size),
    u32(strings.length), u32(0), u32(0x00000100),
    u32(stringsStart), u32(0),
    ...offsets.map(u32),
    blob,
    Buffer.alloc(padding),
  ]);
}

/** 带 8 字节 ResChunk_header 的通用 chunk */
function chunk(type, headerSize, body) {
  return Buffer.concat([u16(type), u16(headerSize), u32(headerSize + body.length), body]);
}

/** ResXMLTree_node 公共头：chunk(8) + lineNumber(4) + comment(4) = 16 字节 */
function xmlNode(type, body, line = 1) {
  const size = 16 + body.length;
  return Buffer.concat([u16(type), u16(16), u32(size), u32(line), u32(0xffffffff), body]);
}

/* --------------------------------- AXML --------------------------------- */

/**
 * 构造 AndroidManifest.xml。
 * @param {object} o
 * @param {string} o.pkg           package 属性
 * @param {number} o.versionCode  android:versionCode
 * @param {string} o.versionName  android:versionName
 * @param {number} o.labelRef     android:label 的资源引用（0 表示直接写字面量）
 * @param {number} o.iconRef      android:icon  的资源引用
 * @param {boolean} o.rawVersionCode 是否给 versionCode 同时写 rawValue（部分打包工具会这么干）
 */
function buildManifestAxml(o) {
  const str = [];
  const idx = new Map();
  const sip = (s) => {
    if (!idx.has(s)) { idx.set(s, str.length); str.push(s); }
    return idx.get(s);
  };

  // 先占位再索引，保证顺序稳定
  const names = [
    'package', 'versionCode', 'versionName', 'manifest', 'uses-sdk',
    'minSdkVersion', 'targetSdkVersion', 'application', 'label', 'icon',
    'activity', 'name', 'intent-filter', 'action', 'category',
    'android', ANDROID_NS,
    'android.intent.action.MAIN', 'android.intent.category.LAUNCHER',
  ];
  names.forEach(sip);

  const ATTR = 20; // ResXMLTree_attribute 固定 20 字节

  function element(name, attrs, build) {
    const attrBufs = attrs.map((a) => {
      // Res_value = size(2) + res0(1) + dataType(1) + data(4)
      const v = a.type === 'string'
        ? Buffer.concat([u16(8), Buffer.from([0, 0x03]), u32(a.valueIdx >>> 0)])
        : Buffer.concat([u16(8), Buffer.from([0, a.dataType]), u32(a.data >>> 0)]);
      return Buffer.concat([
        u32(a.nsIdx === undefined ? 0xffffffff : a.nsIdx),
        u32(a.nameIdx),
        u32(a.rawIdx === undefined ? 0xffffffff : a.rawIdx),
        v,
      ]);
    });
    // ResXMLTree_attrExt = ns(4)+name(4)+attrStart(2)+attrSize(2)+attrCount(2)+idIndex(2) = 16，
    // 但 aapt 生成的 attributeStart 固定为 20，属性区里再跟 4 字节保留位。
    // 解析器按 pos + 16 + attrStart 定位，所以要如实补这 4 字节，否则整块属性错位。
    const body = Buffer.concat([
      u32(0xffffffff), u32(sip(name)),
      u16(20), u16(ATTR), u16(attrs.length), u16(0),
      u32(0),
      ...attrBufs,
    ]);
    const start = xmlNode(0x0102, body);
    const inner = build ? Buffer.concat(build()) : Buffer.alloc(0);
    const end = xmlNode(0x0103, Buffer.concat([u32(0xffffffff), u32(sip(name))]));
    return Buffer.concat([start, inner, end]);
  }

  const nsIdx = sip('android');   // 前缀池索引（注意：这里用同一个池）
  const uriIdx = sip(ANDROID_NS);

  // 属性构造助手
  const androidAttr = (name, val) => ({
    nsIdx: uriIdx,
    nameIdx: sip(name),
    ...val,
  });
  const plainAttr = (name, val) => ({ nsIdx: 0xffffffff, nameIdx: sip(name), ...val });

  const vcAttr = o.rawVersionCode
    ? androidAttr('versionCode', { type: 'typed', dataType: 0x10, data: o.versionCode, rawIdx: sip(String(o.versionCode)) })
    : androidAttr('versionCode', { type: 'typed', dataType: 0x10, data: o.versionCode });

  const manifest = element('manifest', [
    plainAttr('package', { type: 'string', valueIdx: sip(o.pkg) }),
    vcAttr,
    androidAttr('versionName', { type: 'string', valueIdx: sip(o.versionName) }),
  ], () => [
    element('uses-sdk', [
      androidAttr('minSdkVersion', { type: 'typed', dataType: 0x10, data: 24 }),
      androidAttr('targetSdkVersion', { type: 'typed', dataType: 0x10, data: 34 }),
    ]),
    element('application', [
      androidAttr('label', { type: 'typed', dataType: 0x01, data: o.labelRef || 0 }),
      androidAttr('icon', { type: 'typed', dataType: 0x01, data: o.iconRef || 0 }),
    ], () => [
      element('activity', [
        androidAttr('name', { type: 'string', valueIdx: sip('.MainActivity') }),
      ], () => [
        element('intent-filter', [], () => [
          element('action', [
            androidAttr('name', { type: 'string', valueIdx: sip('android.intent.action.MAIN') }),
          ]),
          element('category', [
            androidAttr('name', { type: 'string', valueIdx: sip('android.intent.category.LAUNCHER') }),
          ]),
        ]),
      ]),
    ]),
  ]);

  const pool = stringPool(str);
  const nsStart = xmlNode(0x0100, Buffer.concat([u32(sip('android')), u32(sip(ANDROID_NS))]));
  const nsEnd = xmlNode(0x0101, Buffer.concat([u32(sip('android')), u32(sip(ANDROID_NS))]));
  const resMap = chunk(0x0180, 8, Buffer.alloc(0)); // 空资源映射表（真实 APK 里是属性名资源 ID）

  const body = Buffer.concat([pool, resMap, nsStart, manifest, nsEnd]);
  return Buffer.concat([u16(0x0003), u16(8), u32(8 + body.length), body]);
}

/* --------------------------------- ARSC --------------------------------- */

function tableType(id, entries, keyIdxBase, density = 0) {
  const CONFIG = 64;
  const headerSize = 20 + CONFIG;
  const cfg = Buffer.alloc(CONFIG);
  cfg.writeUInt32LE(CONFIG, 0);
  if (density) cfg.writeUInt16LE(density, 14); // screenType.density
  const offsets = Buffer.alloc(entries.length * 4);
  const vals = [];
  let cur = 0;
  entries.forEach((e, i) => {
    offsets.writeUInt32LE(cur, i * 4);
    const value = Buffer.concat([u16(8), Buffer.from([0, e.dataType]), u32(e.data >>> 0)]);
    const entry = Buffer.concat([u16(8), u16(0), u32(keyIdxBase + i), value]);
    vals.push(entry);
    cur += entry.length;
  });
  const entriesStart = headerSize + offsets.length;
  const body = Buffer.concat([
    Buffer.from([id, 0]), u16(0),
    u32(entries.length), u32(entriesStart),
    cfg,
    offsets, ...vals,
  ]);
  // 注意：body 已含 ResTable_type 头部里 headerSize 之后的部分，
  // 所以 size 必须是 8（chunk header）+ body.length，不能再用 chunk() 的 headerSize + body.length。
  return Buffer.concat([u16(0x0201), u16(headerSize), u32(8 + body.length), body]);
}

/**
 * 构造 resources.arsc。
 * @param {object} o
 * @param {string} o.appName   应用名（string 资源）
 * @param {string} o.iconPath  图标路径（mipmap 资源）
 */
function buildArsc(o) {
  const global = [o.appName, o.iconPath];
  if (o.anydpiXml) global.push(o.anydpiXml);
  const globalPool = stringPool(global);

  const typeStrings = stringPool(['', 'string', 'mipmap']);
  const keyStrings = stringPool(['app_name', 'ic_launcher']);

  const type1 = tableType(1, [{ dataType: 0x03, data: 0 }], 0); // string/app_name -> "测试应用"
  const type2 = tableType(2, [{ dataType: 0x03, data: 1 }], 1); // mipmap/ic_launcher -> png 路径
  // 可选：同一资源在 anydpi 配置下是 adaptive-icon 的 xml（用于验证 score() 的 anydpi 压分）
  const type2any = o.anydpiXml
    ? tableType(2, [{ dataType: 0x03, data: 2 }], 1, 0xfffe)
    : Buffer.alloc(0);
  const subs = [typeStrings, keyStrings, type1, type2, type2any];
  const subsLen = subs.reduce((n, b) => n + b.length, 0);

  // ResTable_package：type(2)+headerSize(2)+size(4)+id(4)+name[128]utf16(256)=268
  // 之后 typeStrings(4)@268、lastPublicType(4)@272、keyStrings(4)@276、lastPublicKey(4)@280、typeIdOffset(4)@284 → 288
  const PKG_HEADER = 288;
  const nameBuf = Buffer.alloc(256);
  nameBuf.write('com.example.demo', 0, 'utf16le');
  const typeStringsOff = PKG_HEADER;
  const keyStringsOff = PKG_HEADER + typeStrings.length;
  const pkgHead = Buffer.concat([
    u16(0x0200), u16(PKG_HEADER),
    u32(PKG_HEADER + subsLen),
    u32(0x7f),
    nameBuf,
    u32(typeStringsOff),
    u32(2),
    u32(keyStringsOff),
    u32(2),
    u32(0),
  ]);
  const pkg = Buffer.concat([pkgHead, ...subs]);

  const headSize = 12;
  const total = headSize + globalPool.length + pkg.length;
  return Buffer.concat([u16(0x0002), u16(headSize), u32(total), u32(1), globalPool, pkg]);
}

/* --------------------------------- ZIP ---------------------------------- */

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c;
  }
  return t;
})();

function crc32(buf) {
  let c = -1;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

/** 最小 ZIP 写入器（deflate 或 stored） */
function writeZip(files) {
  const locals = [];
  const centrals = [];
  let offset = 0;
  for (const f of files) {
    const raw = f.data;
    const comp = f.store ? raw : zlib.deflateRawSync(raw, { level: 9 });
    const method = f.store ? 0 : 8;
    const nameBuf = Buffer.from(f.name, 'utf8');
    const crc = crc32(raw);

    const local = Buffer.alloc(30);
    local.writeUInt32LE(0x04034b50, 0);
    local.writeUInt16LE(20, 4);
    local.writeUInt16LE(0x0800, 6); // UTF-8 名字
    local.writeUInt16LE(method, 8);
    local.writeUInt32LE(crc, 14);
    local.writeUInt32LE(comp.length, 18);
    local.writeUInt32LE(raw.length, 22);
    local.writeUInt16LE(nameBuf.length, 26);
    locals.push(local, nameBuf, comp);

    const cen = Buffer.alloc(46);
    cen.writeUInt32LE(0x02014b50, 0);
    cen.writeUInt16LE(20, 4);
    cen.writeUInt16LE(20, 6);
    cen.writeUInt16LE(0x0800, 8);
    cen.writeUInt16LE(method, 10);
    cen.writeUInt32LE(crc, 16);
    cen.writeUInt32LE(comp.length, 20);
    cen.writeUInt32LE(raw.length, 24);
    cen.writeUInt16LE(nameBuf.length, 28);
    cen.writeUInt32LE(offset, 42);
    centrals.push(cen, nameBuf);

    offset += local.length + nameBuf.length + comp.length;
  }
  const cd = Buffer.concat(centrals);
  const head = Buffer.concat(locals);
  const eocd = Buffer.alloc(22);
  eocd.writeUInt32LE(0x06054b50, 0);
  eocd.writeUInt16LE(files.length, 8);
  eocd.writeUInt16LE(files.length, 10);
  eocd.writeUInt32LE(cd.length, 12);
  eocd.writeUInt32LE(head.length, 16);
  return Buffer.concat([head, cd, eocd]);
}

/* -------------------------------- 组装 APK ------------------------------- */

const PKG = 'com.example.demo';
const LABEL = '测试应用';
const ICON_FILE = 'res/mipmap-xxxhdpi/ic_launcher.png';

function sampleApkBuffer(opts = {}) {
  const o = {
    pkg: PKG,
    versionCode: 42,
    versionName: '1.4.2',
    labelRef: 0x7f010000, // string/app_name
    iconRef: 0x7f020000,  // mipmap/ic_launcher
    rawVersionCode: false,
    ...opts,
  };
  const manifest = buildManifestAxml(o);
  const arsc = buildArsc({ appName: LABEL, iconPath: ICON_FILE });
  const png = encodePng(48, 48, pngRgba(48));

  return writeZip([
    { name: 'AndroidManifest.xml', data: manifest },
    { name: 'resources.arsc', data: arsc },
    { name: ICON_FILE, data: png },
    { name: 'classes.dex', data: Buffer.from('dex\n035\0' + '\0'.repeat(104)), store: true },
    { name: 'lib/arm64-v8a/libdemo.so', data: Buffer.from('\x7fELF' + '\0'.repeat(60)), store: true },
  ]);
}

/** 生成一张简单的 48x48 RGBA 渐变图（不依赖 png.js 的内部细节） */
function pngRgba(size) {
  const px = new Uint8Array(size * size * 4);
  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      const i = (y * size + x) * 4;
      px[i] = (x * 255 / size) | 0;
      px[i + 1] = (y * 255 / size) | 0;
      px[i + 2] = 180;
      px[i + 3] = 255;
    }
  }
  return px;
}

function buildSampleApk(dir, name = 'sample.apk', opts) {
  fs.mkdirSync(dir, { recursive: true });
  const file = path.join(dir, name);
  fs.writeFileSync(file, sampleApkBuffer(opts));
  return file;
}

module.exports = {
  buildSampleApk,
  sampleApkBuffer,
  buildManifestAxml,
  buildArsc,
  writeZip,
  PKG,
  LABEL,
  ICON_FILE,
  ANDROID_NS,
};

if (require.main === module) {
  const out = process.argv[2] || path.join(__dirname, 'sample.apk');
  const file = buildSampleApk(path.dirname(out), path.basename(out));
  console.log(`已生成 ${file}（${fs.statSync(file).size} 字节）`);
}
