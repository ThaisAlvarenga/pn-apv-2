// PN JUNCTION + WRIST SLIDER + HAND JOINT CUBES (CURL COLORS) + HAND-ONLY NAVIGATION
// NOTE: Hand-gesture navigation runs ONLY when hands are present AND Oculus/Quest controllers are NOT present.

// ------------------- Imports -------------------
import * as THREE from 'https://unpkg.com/three@0.163.0/build/three.module.js';
import { MathUtils } from 'https://unpkg.com/three@0.163.0/src/math/MathUtils.js';
import { ImprovedNoise } from 'https://unpkg.com/three@0.163.0/examples/jsm/math/ImprovedNoise.js';
import * as BufferGeometryUtils from 'https://unpkg.com/three@0.163.0/examples/jsm/utils/BufferGeometryUtils.js';
import { Vector3 } from 'https://unpkg.com/three@0.163.0/src/math/Vector3.js';
import { TransformControls } from 'https://unpkg.com/three@0.163.0/examples/jsm/controls/TransformControls.js';
import { OrbitControls } from 'https://unpkg.com/three@0.163.0/examples/jsm/controls/OrbitControls.js';
import { XRButton } from 'https://unpkg.com/three@0.163.0/examples/jsm/webxr/XRButton.js';
import { XRControllerModelFactory } from 'https://unpkg.com/three@0.163.0/examples/jsm/webxr/XRControllerModelFactory.js';
import { TextGeometry } from 'https://unpkg.com/three@0.163.0/examples/jsm/geometries/TextGeometry.js';
import { FontLoader } from 'https://unpkg.com/three@0.163.0/examples/jsm/loaders/FontLoader.js';
import { RGBELoader } from 'https://unpkg.com/three@0.163.0/examples/jsm/loaders/RGBELoader.js';

import * as Generation from "./generationUtil.js";
import * as Recombination from "./recombinationUtil.js";
import * as SphereUtil from "./sphere.js";

// ------------------- Globals / Setup -------------------
const hdrFile = "./assets/black.hdr";

var container, camera, renderer;
var voltageLevel;
var cameraControls;
var gui;
const voltageControl = document.getElementById('voltage');
var minScalar = 0.22;
var maxScalar = 0.88;
var cube1;
var holeColor = 0xd55e00;
var electronColor = 0x56b4e9;

// PN Junction Initial Variables
var electronSpheres = [];
var holeSpheres = [];
var numSpheres = 50;

var cubeSize = new THREE.Vector3(150, 75, 75);
var clock = new THREE.Clock();

var boxMin = -(cubeSize.x/2) + 1;
var boxMax = (cubeSize.x/2) - 1;

// electric field attributes
var arrowNegative;
var innerBoxSize = 25;
var innerCubeGeometry;
var innerCubeMaterial;
var innerCube;
var voltage = 0.0;
const arrowColor = 0xf0e442;

// text components in 3d scene
var positiveSign = "(+)";
var negativeSign = "(-)";
var chargeTextMesh_pos;
var chargeTextMesh_neg;
var positiveSignGeometry;
var negativeSignGeometry;

var eSignText = "E";
var eSignTextMesh;
var eSignGeometry;

const TRIGGER_THRESHOLD = 0.1;
const THUMB_TURN_SPEED = 1.2;     // radians/sec (tweak)
const THUMB_TURN_DEADZONE = 0.0;  // optional; keep 0 since it’s boolean


// scatter variables
var scatterTimeMean = 2;
const perlin = new ImprovedNoise();

// battery variables
var positiveBatteryElements = [];
var negativeBatteryElements = [];
let batteryAdded = false;

let voltageChangedOnce = false;

// populate boltz distribution table
var boltz = [];

// recombination variables
var minDistance = 30;
var e_sphere_outside_depvarion_range = false;
var h_sphere_outside_depvarion_range = false;
var recombination_orbs = [];

// generation variables
var generatedPairs = [];

// VR control variables
var controller1, controller2;
var controllerGrip1, controllerGrip2;
var dolly;
var xrSession = null;

// controller states
const controllerStates = {
  leftController: {
    thumbstick: {x:0, y:0},
    trigger: 0,
    triggerPressed: false,
    triggerPressedLastFrame: false,
    isVisionProSource: false,
    inputSource: null
  },
  rightController: {
    thumbstick: {x:0, y:0},
    trigger: 0,
    triggerPressed: false,
    triggerPressedLastFrame: false,
    isVisionProSource: false,
    inputSource: null
  }
};

const WORLD_UP = new THREE.Vector3(0, 1, 0);
let orbit = null;
let _lastT = null; // ms from XR animation loop

// movement settings
const vrSettings = {
  moveSpeed: 2,
  rotationSpeed: 0.05
};

const loader = new FontLoader();
var scene = new THREE.Scene();


// ========================= Wrist Slider (left wrist; right-hand pinch) =========================

// --- Config
const SLIDER_MIN = -1.4;
const SLIDER_MAX =  0.4;
const TRACK_LEN_M = 0.18;         // ~18 cm
const PINCH_THRESHOLD_M = 0.018;  // ~1.8 cm

// --- State shared with your sim
let sliderValue = 0.0;   // will drive `voltage`

// --- Scene nodes
const sliderRoot  = new THREE.Object3D(); // follows left wrist (fallback: left grip)
const sliderTilt  = new THREE.Object3D();
const sliderPanel = new THREE.Object3D();

let sliderTrack = null;
let sliderKnob  = null;

let labelCanvas, labelCtx, labelTex, labelMesh;

// gizmo dot
const rayDot = new THREE.Mesh(
  new THREE.SphereGeometry(0.008, 12, 12),
  new THREE.MeshBasicMaterial({ color: 0x66ff88 })
);
sliderRoot.add(rayDot);

function setVoltage(v) {
  const clamped = THREE.MathUtils.clamp(v, SLIDER_MIN, SLIDER_MAX);
  voltage = clamped;
  sliderValue = clamped;

  if (sliderKnob) sliderKnob.position.x = valueToX(clamped);
  drawVoltageLabel(clamped);

  const myTextEl = document.getElementById('myText');
  if (myTextEl) myTextEl.textContent = clamped.toFixed(2);

  if (voltageControl) voltageControl.value = clamped;
}

// helpers
const valueToX = (v) => THREE.MathUtils.mapLinear(v, SLIDER_MIN, SLIDER_MAX, -TRACK_LEN_M/2, TRACK_LEN_M/2);
const xToValue = (x) => THREE.MathUtils.clamp(
  THREE.MathUtils.mapLinear(x, -TRACK_LEN_M/2, TRACK_LEN_M/2, SLIDER_MIN, SLIDER_MAX),
  SLIDER_MIN, SLIDER_MAX
);

// refs to XR state
let xrRefSpace_local = null;
let leftHandSource   = null;
let rightHandSource  = null;

// utility: find a specific hand source
function findHand(session, handedness) {
  if (!session) return null;
  for (const src of session.inputSources) {
    if (src.hand && src.handedness === handedness) return src;
  }
  return null;
}

function updateLeftRightHandSources(session) {
  leftHandSource  = findHand(session, 'left');
  rightHandSource = findHand(session, 'right');
}

// Build slider UI and register XR listeners
function initWristSlider() {
  // IMPORTANT: attach to dolly so slider moves with locomotion
  // (dolly must exist already -> call setUpVRControls() before initWristSlider())
  if (dolly) dolly.add(sliderRoot);
  else scene.add(sliderRoot); // fallback (shouldn't happen)

  sliderRoot.add(sliderTilt);
  sliderTilt.add(sliderPanel);

  // backing
  const bg = new THREE.Mesh(
    new THREE.PlaneGeometry(0.22, 0.10),
    new THREE.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.45 })
  );
  bg.position.z = -0.001;
  sliderPanel.add(bg);

  // track
  sliderTrack = new THREE.Mesh(
    new THREE.PlaneGeometry(TRACK_LEN_M, 0.02),
    new THREE.MeshBasicMaterial({ color: 0x222222, transparent: true, opacity: 0.85 })
  );
  sliderPanel.add(sliderTrack);

  // knob
  sliderKnob = new THREE.Mesh(
    new THREE.CircleGeometry(0.015, 32),
    new THREE.MeshBasicMaterial({ color: 0xffcc66 })
  );
  sliderKnob.position.set(valueToX(sliderValue), 0, 0.001);
  sliderPanel.add(sliderKnob);

  // ------------------- NAV TOGGLE BUTTON (on wrist panel) -------------------
  // [NAV TOGGLE]
  navCanvas = document.createElement('canvas');
  navCanvas.width = 1024;
  navCanvas.height = 256;
  navCtx = navCanvas.getContext('2d');

  navTex = new THREE.CanvasTexture(navCanvas);
  navTex.colorSpace = THREE.SRGBColorSpace;
  navTex.minFilter = THREE.LinearFilter;
  navTex.magFilter = THREE.LinearFilter;

  navButtonMesh = new THREE.Mesh(
    new THREE.PlaneGeometry(NAV_BTN_W, NAV_BTN_H),
    new THREE.MeshBasicMaterial({
      map: navTex,
      transparent: true,
      depthTest: false,
      depthWrite: false
    })
  );

  // place button above the track
  navButtonMesh.position.set(0, NAV_BTN_Y, 0.006);
  sliderPanel.add(navButtonMesh);

  // initial label
  setNavigationEnabled(navigationEnabled);


  // label (canvas)
  labelCanvas = document.createElement('canvas');
  labelCanvas.width = 1024; labelCanvas.height = 256;
  labelCtx = labelCanvas.getContext('2d');

  labelTex = new THREE.CanvasTexture(labelCanvas);
  labelTex.colorSpace = THREE.SRGBColorSpace;
  labelTex.minFilter = THREE.LinearFilter;
  labelTex.magFilter = THREE.LinearFilter;

  labelMesh = new THREE.Mesh(
    new THREE.PlaneGeometry(0.30, 0.09),
    new THREE.MeshBasicMaterial({ map: labelTex, transparent: true, depthTest: false, depthWrite: false })
  );
  labelMesh.position.set(0, 0.09, 0.006);
  sliderPanel.add(labelMesh);

  // local placement near the wrist (tweak)
  sliderPanel.position.set(0.07, 0.02, -0.05);
  sliderPanel.rotation.set(
    THREE.MathUtils.degToRad(45),
    THREE.MathUtils.degToRad(25),
    THREE.MathUtils.degToRad(-90)
  );

  drawVoltageLabel(sliderValue);

  // XR session lifecycle
  renderer.xr.addEventListener('sessionstart', async () => {
    const s = renderer.xr.getSession();
    try { xrRefSpace_local = await s.requestReferenceSpace('local-floor'); } catch {}
    updateLeftRightHandSources(s);
    s.addEventListener('inputsourceschange', () => updateLeftRightHandSources(s));
  });

  renderer.xr.addEventListener('sessionend', () => {
    xrRefSpace_local = null;
    leftHandSource = rightHandSource = null;
  });
}

function drawVoltageLabel(v) {
  if (!labelCtx) return;
  const W = labelCanvas.width, H = labelCanvas.height;
  labelCtx.clearRect(0,0,W,H);
  labelCtx.fillStyle = 'rgba(0,0,0,0.55)';
  labelCtx.fillRect(0,0,W,H);
  labelCtx.fillStyle = '#ffffff';
  labelCtx.font = 'bold 120px system-ui, -apple-system, Segoe UI, Roboto, sans-serif';
  labelCtx.textAlign = 'center';
  labelCtx.textBaseline = 'middle';
  labelCtx.fillText(`Voltage: ${v.toFixed(2)} V`, W/2, H/2);
  labelTex.needsUpdate = true;
}

// Pose the slider at the left wrist (fallback: left controller grip)
const _tmpObj = new THREE.Object3D();

function updateSliderPose(frame) {
  const session = renderer.xr.getSession?.();
  if (!session) { sliderRoot.visible = false; return; }

  // Prefer hand wrist
  if (leftHandSource && leftHandSource.hand && xrRefSpace_local && frame) {
    const ht = leftHandSource.hand;
    const wrist = ht.get?.('wrist') || (typeof XRHand!=='undefined' && ht[XRHand.WRIST]);
    if (wrist) {
      const pose = frame.getJointPose(wrist, xrRefSpace_local);
      if (pose) {
        const t = pose.transform;
        sliderRoot.position.set(t.position.x, t.position.y, t.position.z);
        sliderRoot.quaternion.set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w);
        sliderRoot.visible = true;
        return;
      }
    }
  }

  // Fallback: left controller grip(0)
  const grip = renderer.xr.getControllerGrip?.(0);
  if (grip) {
    _tmpObj.matrix.copy(grip.matrixWorld);
    _tmpObj.matrix.decompose(sliderRoot.position, sliderRoot.quaternion, sliderRoot.scale);
    sliderRoot.visible = true;
    return;
  }

  sliderRoot.visible = false;
}

// Right-hand pinch to drag along the track
function updateSliderInteraction(frame) {
  if (!xrRefSpace_local || !frame) return;
  const session = renderer.xr.getSession?.();
  if (!session) return;

  const rhs = findHand(session, 'right') || rightHandSource;
  if (!rhs || !rhs.hand) return;

  const ht = rhs.hand;
  const tipIndex = ht.get?.('index-finger-tip') || (typeof XRHand!=='undefined' && XRHand.INDEX_PHALANX_TIP);
  const tipThumb = ht.get?.('thumb-tip')        || (typeof XRHand!=='undefined' && XRHand.THUMB_PHALANX_TIP);
  if (!tipIndex || !tipThumb) return;

  const pI = frame.getJointPose(tipIndex, xrRefSpace_local);
  const pT = frame.getJointPose(tipThumb, xrRefSpace_local);
  if (!pI || !pT) return;

  const dx = pI.transform.position.x - pT.transform.position.x;
  const dy = pI.transform.position.y - pT.transform.position.y;
  const dz = pI.transform.position.z - pT.transform.position.z;
  const dist = Math.sqrt(dx*dx + dy*dy + dz*dz);

  const pinching = dist < PINCH_THRESHOLD_M;

  // [NAV TOGGLE] reset latch when pinch is released
  if (!pinching) {
    navToggleLatched = false;
    return;
  }

  // Project index tip to slider local space
  const idxWorld = new THREE.Vector3(
    pI.transform.position.x,
    pI.transform.position.y,
    pI.transform.position.z
  );

  // slider is under `dolly`, so move the XR joint point into the same space
  if (dolly) idxWorld.applyMatrix4(dolly.matrixWorld);

  const local = sliderPanel.worldToLocal(idxWorld.clone());

  // [NAV TOGGLE] 1) BUTTON HIT TEST (priority over slider dragging)
  const hitNav =
    Math.abs(local.x - 0) <= (NAV_BTN_W * 0.5) &&
    Math.abs(local.y - NAV_BTN_Y) <= (NAV_BTN_H * 0.5);

  if (hitNav) {
    if (!navToggleLatched) {
      setNavigationEnabled(!navigationEnabled);
      navToggleLatched = true;
    }
    return; // don't also drag slider on same pinch
  }

  // 2) SLIDER DRAG
  const clampedX = THREE.MathUtils.clamp(local.x, -TRACK_LEN_M/2, TRACK_LEN_M/2);
  const newV = xToValue(clampedX);

  sliderKnob.position.x = THREE.MathUtils.lerp(sliderKnob.position.x, clampedX, 0.35);
  setVoltage(newV);
}


function getSliderValue() { return sliderValue; }

// ========================= Wrist Nav Toggle (on wrist panel) =========================
// [NAV TOGGLE]
let navigationEnabled = true;

// 3D button pieces
let navButtonMesh = null;
let navCanvas = null, navCtx = null, navTex = null;

// debounce latch (toggle once per pinch)
let navToggleLatched = false;

// button layout in sliderPanel local space
const NAV_BTN_W = 0.10;   // meters
const NAV_BTN_H = 0.032;  // meters
const NAV_BTN_Y = 1;   // above the slider track (track is y=0)

// Draw + update helpers
function drawNavButtonLabel() {
  if (!navCtx || !navCanvas || !navTex) return;

  const W = navCanvas.width, H = navCanvas.height;
  navCtx.clearRect(0, 0, W, H);

  // background
  navCtx.fillStyle = navigationEnabled ? 'rgba(30,130,60,0.85)' : 'rgba(140,40,40,0.85)';
  navCtx.fillRect(0, 0, W, H);

  // border
  navCtx.strokeStyle = 'rgba(255,255,255,0.65)';
  navCtx.lineWidth = 12;
  navCtx.strokeRect(10, 10, W - 20, H - 20);

  // text
  navCtx.fillStyle = '#fff';
  navCtx.font = 'bold 120px system-ui, -apple-system, Segoe UI, Roboto, sans-serif';
  navCtx.textAlign = 'center';
  navCtx.textBaseline = 'middle';
  navCtx.fillText(`NAV: ${navigationEnabled ? 'ON' : 'OFF'}`, W / 2, H / 2);

  navTex.needsUpdate = true;
}

function setNavigationEnabled(on) {
  navigationEnabled = !!on;
  drawNavButtonLabel();
}



// ========================= HAND DEBUG + HAND-ONLY NAVIGATION =========================

// 25 joints
const JOINT_COUNT = 25;
const jointRadii = new Float32Array(JOINT_COUNT);
const jointMatrices = new Float32Array(16 * JOINT_COUNT);

const HAND_JOINT_NAMES = [
  'wrist',

  'thumb-metacarpal',
  'thumb-phalanx-proximal',
  'thumb-phalanx-distal',
  'thumb-tip',

  'index-finger-metacarpal',
  'index-finger-phalanx-proximal',
  'index-finger-phalanx-intermediate',
  'index-finger-phalanx-distal',
  'index-finger-tip',

  'middle-finger-metacarpal',
  'middle-finger-phalanx-proximal',
  'middle-finger-phalanx-intermediate',
  'middle-finger-phalanx-distal',
  'middle-finger-tip',

  'ring-finger-metacarpal',
  'ring-finger-phalanx-proximal',
  'ring-finger-phalanx-intermediate',
  'ring-finger-phalanx-distal',
  'ring-finger-tip',

  'pinky-finger-metacarpal',
  'pinky-finger-phalanx-proximal',
  'pinky-finger-phalanx-intermediate',
  'pinky-finger-phalanx-distal',
  'pinky-finger-tip'
];

const FINGERS = {
  thumb:  { base: 'thumb-metacarpal',           tip: 'thumb-tip' },
  index:  { base: 'index-finger-metacarpal',    tip: 'index-finger-tip' },
  middle: { base: 'middle-finger-metacarpal',   tip: 'middle-finger-tip' },
  ring:   { base: 'ring-finger-metacarpal',     tip: 'ring-finger-tip' },
  pinky:  { base: 'pinky-finger-metacarpal',    tip: 'pinky-finger-tip' }
};

// thresholds (meters)
const FINGER_THRESHOLDS = {
  thumb:  0.090, // your observed ~0.08 curled vs ~0.10 extended → 0.09 split
  index:  0.065,
  middle: 0.055,
  ring:   0.055,
  pinky:  0.050
};

const handState = {
  left:  { curls: {}, palm: '—' },
  right: { curls: {}, palm: '—' }
};

const handDebugRoot = {
  left:  new THREE.Object3D(),
  right: new THREE.Object3D()
};

const handJointMeshes = {
  left:  new Map(),
  right: new Map()
};

const jointPositions = {
  left:  {},
  right: {}
};

const handPalmMeshes = {
  left: null,
  right: null
};

// temps
const _mPose = new THREE.Matrix4();
const _mInvParent = new THREE.Matrix4();
const _mLocal = new THREE.Matrix4();
const _q = new THREE.Quaternion();
const _p = new THREE.Vector3();
const _s = new THREE.Vector3();
const _v1 = new THREE.Vector3();
const _v2 = new THREE.Vector3();
const _v3 = new THREE.Vector3();

function getHandJointSpace(xrHand, jointName) {
  if (!xrHand) return null;
  if (xrHand.get) return xrHand.get(jointName) || null;
  if (typeof XRHand !== 'undefined') {
    const key = jointName.toUpperCase().replace(/-/g, '_');
    if (XRHand[key] !== undefined) return xrHand[XRHand[key]] || null;
  }
  return null;
}

function setFromXRPoseUnderParent(obj, xrPose, parent) {
  const t = xrPose.transform;
  _mPose.compose(
    _p.set(t.position.x, t.position.y, t.position.z),
    _q.set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w),
    _s.set(1, 1, 1)
  );

  parent.updateMatrixWorld(true);
  _mInvParent.copy(parent.matrixWorld).invert();
  _mLocal.multiplyMatrices(_mInvParent, _mPose);
  _mLocal.decompose(obj.position, obj.quaternion, obj.scale);
}

function initHandDebugMeshes() {
  // Attach debug roots to dolly so they move with locomotion
  dolly.add(handDebugRoot.left);
  dolly.add(handDebugRoot.right);

  const jointGeom = new THREE.BoxGeometry(0.2, 0.2, 0.2);
  const leftColor  = new THREE.Color(0x56B4E9);
  const rightColor = new THREE.Color(0x56B4E9);

  ['left', 'right'].forEach((handedness) => {
    const isLeft = handedness === 'left';
    const baseColor = isLeft ? leftColor : rightColor;

    HAND_JOINT_NAMES.forEach((jointName) => {
      const mat = new THREE.MeshBasicMaterial({
        color: baseColor.clone(),
        transparent: true,
        opacity: 0.9
      });
      const mesh = new THREE.Mesh(jointGeom, mat);
      mesh.visible = false;
      handDebugRoot[handedness].add(mesh);
      handJointMeshes[handedness].set(jointName, mesh);
    });

    const palmGeom = new THREE.BoxGeometry(0.04, 0.025, 0.006);
    const palmMat  = new THREE.MeshBasicMaterial({
      color: baseColor.clone(),
      transparent: true,
      opacity: 0.95
    });
    const palmMesh = new THREE.Mesh(palmGeom, palmMat);
    palmMesh.visible = false;
    handDebugRoot[handedness].add(palmMesh);
    handPalmMeshes[handedness] = palmMesh;
  });
}

function updateHandDebug(frame, refSpace) {
  const session = renderer.xr.getSession?.();
  if (!session || !frame || !refSpace) return;

  dolly.updateMatrixWorld(true);

  ['left', 'right'].forEach((handedness) => {
    const src = findHand(session, handedness);
    const jointMap = handJointMeshes[handedness];
    const palmMesh = handPalmMeshes[handedness];

    jointPositions[handedness] = {};

    if (!src || !src.hand) {
      jointMap.forEach(m => m.visible = false);
      if (palmMesh) palmMesh.visible = false;
      return;
    }

    const hand = src.hand;

    if (!frame.fillJointRadii(hand.values(), jointRadii)) {
      jointMap.forEach(m => m.visible = false);
      if (palmMesh) palmMesh.visible = false;
      return;
    }

    if (!frame.fillPoses(hand.values(), refSpace, jointMatrices)) {
      jointMap.forEach(m => m.visible = false);
      if (palmMesh) palmMesh.visible = false;
      return;
    }

    // apply joint transforms in dolly-local space
    for (let jIndex = 0; jIndex < HAND_JOINT_NAMES.length; jIndex++) {
      const jointName = HAND_JOINT_NAMES[jIndex];
      const mesh = jointMap.get(jointName);
      if (!mesh) continue;

     _mPose.fromArray(jointMatrices, jIndex * 16);

// IMPORTANT: do NOT convert into dolly-local using inv(dolly).
// These meshes are already children of `dolly`, so we want the XR pose
// to be applied in dolly space so the hands move with locomotion.
_mPose.decompose(mesh.position, mesh.quaternion, mesh.scale);


      const radius = jointRadii[jIndex] || 0.008;
      mesh.scale.setScalar(radius * 2.0);
      mesh.visible = true;

      jointPositions[handedness][jointName] = mesh.position.clone();
    }

    // curl detection
    const baseHex   = handedness === 'left' ? 0xff00ff : 0x00ffff;
    const curledHex = 0xff5555;

    for (const fingerName in FINGERS) {
      const def = FINGERS[fingerName];
      const basePos = jointPositions[handedness][def.base];
      const tipPos  = jointPositions[handedness][def.tip];
      if (!basePos || !tipPos) continue;

      const extension = basePos.distanceTo(tipPos);
      const threshold = FINGER_THRESHOLDS[fingerName] ?? 0.055;
      const isCurled = extension < threshold;

      handState[handedness].curls[fingerName] = isCurled;

      const tipMesh = jointMap.get(def.tip);
      if (tipMesh) tipMesh.material.color.setHex(isCurled ? curledHex : baseHex);
    }

    // palm orientation (optional)
    if (palmMesh) {
      const wristSpace = getHandJointSpace(hand, 'wrist');
      const indexMeta  = getHandJointSpace(hand, 'index-finger-metacarpal');
      const pinkyMeta  = getHandJointSpace(hand, 'pinky-finger-metacarpal');
      const middleMeta = getHandJointSpace(hand, 'middle-finger-metacarpal');

      const wristPose  = wristSpace  ? frame.getJointPose(wristSpace,  refSpace) : null;
      const indexPose  = indexMeta   ? frame.getJointPose(indexMeta,   refSpace) : null;
      const pinkyPose  = pinkyMeta   ? frame.getJointPose(pinkyMeta,   refSpace) : null;
      const middlePose = middleMeta  ? frame.getJointPose(middleMeta,  refSpace) : null;

      if (wristPose && indexPose && pinkyPose && middlePose) {
        const w = wristPose.transform.position;
        const i = indexPose.transform.position;
        const p = pinkyPose.transform.position;
        const m = middlePose.transform.position;

        const wristWorld = _v1.set(w.x, w.y, w.z);
        const idxWorld   = _v2.set(i.x, i.y, i.z);
        const pnkWorld   = _v3.set(p.x, p.y, p.z);
        const midWorld   = new THREE.Vector3(m.x, m.y, m.z);

        const vSide    = pnkWorld.clone().sub(idxWorld);
        const vForward = midWorld.clone().sub(wristWorld);
        const palmNormalWorld = vSide.clone().cross(vForward).normalize();
        if (handedness === 'right') palmNormalWorld.multiplyScalar(-1);

        const t = wristPose.transform;
palmMesh.position.set(t.position.x, t.position.y, t.position.z);
palmMesh.quaternion.set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w);

        palmMesh.visible = true;

        const dotUp = palmNormalWorld.dot(WORLD_UP);
        if (dotUp > 0.5) {
          palmMesh.material.color.setHex(0x55ff55);
          handState[handedness].palm = 'UP';
        } else if (dotUp < -0.5) {
          palmMesh.material.color.setHex(0xff5555);
          handState[handedness].palm = 'DOWN';
        } else {
          palmMesh.material.color.setHex(handedness === 'left' ? 0x5555ff : 0x55ffff);
          handState[handedness].palm = 'SIDE';
        }
      } else {
        palmMesh.visible = false;
      }
    }
  });
}

function hasHands(session) {
  if (!session) return false;
  for (const src of session.inputSources) {
    if (src.hand) return true;
  }
  return false;
}

// treat Quest/Touch-style controllers as "oculus controllers"
function hasOculusControllers(session) {
  if (!session) return false;
  for (const src of session.inputSources) {
    if (!src.gamepad) continue;
    const h = src.handedness || 'none';
    if ((h === 'left' || h === 'right') && !isVisionProInputSource(src)) {
      return true;
    }
  }
  return false;
}

// Your gestures:
// - RIGHT: pinky+ring+middle curled => move forward
// - LEFT:  index+middle+ring+pinky curled => move backward
function applyHandGestureLocomotion(frame) {
  if (!renderer.xr.isPresenting) return;

  // [NAV TOGGLE]
  if (!navigationEnabled) return;

  const session = renderer.xr.getSession?.();
  if (!session) return;

  // Only when hands are active and Oculus controllers are NOT present
  if (!hasHands(session)) return;
  if (hasOculusControllers(session)) return;

  const right = handState.right.curls;
  const left  = handState.left.curls;

  const moveForward = !!right.middle && !!right.ring && !!right.pinky;
  const moveBackward = !!left.index && !!left.middle && !!left.ring && !!left.pinky;

  if (!moveForward && !moveBackward) return;

  const forward = new THREE.Vector3();
  camera.getWorldDirection(forward);
  forward.y = 0;
  if (forward.lengthSq() < 1e-6) return;
  forward.normalize();

  const step = vrSettings.moveSpeed * 0.6; // tweak
  if (moveForward) dolly.position.addScaledVector(forward, step);
  if (moveBackward) dolly.position.addScaledVector(forward, -step);
}

// Gesture: thumb curl to rotate left/right

function applyThumbTurn(dt) {
  // [NAV TOGGLE]
  if (!navigationEnabled) return;

  // Only rotate when we're actually in XR and using a dolly
  if (!renderer.xr.isPresenting || !dolly) return;

  const session = renderer.xr.getSession?.();
  if (!session) return;

  // ✅ Hand-tracking only: if any gamepad (Quest controllers) is present, do nothing
  const hasAnyController = [...session.inputSources].some(src => !!src.gamepad && !src.hand);
  const hasAnyHands = [...session.inputSources].some(src => !!src.hand);
  if (!hasAnyHands || hasAnyController) return;

  const leftThumbCurled  = !!handState.left?.curls?.thumb;
  const rightThumbCurled = !!handState.right?.curls?.thumb;

  // If both thumbs curled, cancel out (no rotation). You can change this if you want.
  if (leftThumbCurled && rightThumbCurled) return;

  if (rightThumbCurled) {
    dolly.rotation.y -= THUMB_TURN_SPEED * dt; // rotate right
  } else if (leftThumbCurled) {
    dolly.rotation.y += THUMB_TURN_SPEED * dt; // rotate left
  }
}


// ========================= App Boot =========================
init();
update();

// (You had these duplicated; keeping one pair is usually enough, but leaving as-is if you really want it)
setInterval(() => {
  let generatedPair = Generation.generatePair(cubeSize);
  scene.add(generatedPair.orbSphere);
  scene.add(generatedPair.electron.object);
  scene.add(generatedPair.hole.object);
  generatedPairs.push(generatedPair);
}, 2000);

setInterval(() => {
  Recombination.recombinationOrbRemove(recombination_orbs, scene);
}, 2000);


// ========================= Init =========================
function init() {
  // populate boltz distribution table
  const norm_vel = [
    {nv: 0.1, quantity: 3}, {nv: 0.2, quantity: 10}, {nv: 0.3, quantity: 21}, {nv: 0.4, quantity: 35},
    {nv: 0.5, quantity: 49}, {nv: 0.6, quantity: 63}, {nv: 0.7, quantity: 74}, {nv: 0.8, quantity: 82},
    {nv: 0.9, quantity: 86}, {nv: 1.0, quantity: 86}, {nv: 1.1, quantity: 83}, {nv: 1.2, quantity: 77},
    {nv: 1.3, quantity: 69}, {nv: 1.4, quantity: 59}, {nv: 1.5, quantity: 50}, {nv: 1.6, quantity: 40},
    {nv: 1.7, quantity: 32}, {nv: 1.8, quantity: 24}, {nv: 1.9, quantity: 18}, {nv: 3.0, quantity: 13},
    {nv: 2.1, quantity: 9},  {nv: 2.2, quantity: 6},  {nv: 2.3, quantity: 4},  {nv: 3.5, quantity: 3},
    {nv: 4, quantity: 2},    {nv: 5, quantity: 1},    {nv: 6, quantity: 1}
  ];
  for (var i = 0; i < norm_vel.length; i++) {
    var count = 0;
    while (count < norm_vel[i].quantity) {
      boltz.push(norm_vel[i].nv);
      count++;
    }
  }

  container = document.getElementById('three-container-scene-1');
  if (!container) {
    console.error('Container not found');
    return;
  }

  new RGBELoader()
    .load(hdrFile, function (texture) {
      scene.background = texture;
      scene.environment = texture;
    }, undefined, function (error) {
      console.error("Failed to load HDR file:", error);
    });

  // camera
  camera = new THREE.PerspectiveCamera(75, container.clientWidth / container.clientHeight, 0.1, 1500);
  camera.position.set(0, 0, 150);

  // renderer
  renderer = new THREE.WebGLRenderer({ alpha: false });
  renderer.setSize(container.clientWidth, container.clientHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.xr.enabled = true;
  renderer.xr.setReferenceSpaceType('local-floor');

  initXR();
  container.appendChild(renderer.domElement);

  // ---------------- Desktop OrbitControls (browser only) ----------------
orbit = new OrbitControls(camera, renderer.domElement);
orbit.enableDamping = true;
orbit.dampingFactor = 0.08;

// Pick a nice desktop orbit target (center of your PN junction)
orbit.target.set(0, 0, 0);

// Optional: limit crazy zooming / flipping in desktop mode
orbit.minDistance = 20;
orbit.maxDistance = 800;
orbit.enablePan = true;

orbit.update();

// Auto-toggle when entering/leaving XR
renderer.xr.addEventListener('sessionstart', () => {
  if (orbit) orbit.enabled = false;       // XR owns the camera pose
});

renderer.xr.addEventListener('sessionend', () => {
  if (orbit) {
    orbit.enabled = true;
    orbit.update();
  }
});


  // XR CONTROLS
  container.appendChild(XRButton.createButton(renderer, {
    requiredFeatures: ['local-floor'],
    optionalFeatures: ['hand-tracking']
  }));

  // IMPORTANT ORDER:
  // 1) create dolly/controllers
  setUpVRControls();

  // 2) slider attaches to dolly + tracks hands/pinch
  initWristSlider();

  // 3) joint cubes attach to dolly
  initHandDebugMeshes();

  // If your HTML slider has an initial value, use it; otherwise set 0.
  const startV = parseFloat(voltageControl?.value ?? '0') || 0;
  setVoltage(startV);

  // lighting
  const light = new THREE.AmbientLight(0xffffff, 1);
  scene.add(light);

  const directionalLight = new THREE.DirectionalLight(0xffffff, 1);
  directionalLight.position.set(1, 1, 1).normalize();
  scene.add(directionalLight);

  // GUI
  gui = new dat.GUI({autoPlace: false});
  gui.domElement.style.position = 'relative';
  gui.domElement.style.right = '0px';
  gui.domElement.style.top = '10px';

  cameraControls = {
    translateZ : 150,
    translateX: 0,
    rotateY: MathUtils.degToRad(0),
  };

  voltageLevel = { x: 0.0 };

  document.getElementById("myText").innerHTML = 0;

  gui.add(cameraControls, 'translateX', -100, 100).onChange(() => {
    camera.position.x = cameraControls.translateX;
  });
  gui.add(cameraControls, 'translateZ', -50, 150).onChange(() => {
    camera.position.z = cameraControls.translateZ;
  });
  gui.add(cameraControls, 'rotateY', -50, 50).onChange(() => {
    camera.rotation.y = MathUtils.degToRad(cameraControls.rotateY);
  });

  const thermalControls = { scalar: SphereUtil.getScalar() };
//   gui.add(thermalControls, 'scalar', 0.001, 1.5, 0.01)
//     .name('Sphere Scalar')
//     .onChange((v) => {
//       SphereUtil.setScalar(v);
//     });

  const resetButton = { 'Reset Cube': resetGUI };
  gui.add(resetButton, 'Reset Cube');

  container.appendChild(gui.domElement);

  // DOM slider -> setVoltage (keeps VR slider + voltage synced)
  voltageControl?.addEventListener('input', () => {
    setVoltage(parseFloat(voltageControl.value));
  });

  window.addEventListener('resize', onWindowResize);

  // text
  loader.load('https://unpkg.com/three@0.163.0/examples/fonts/helvetiker_regular.typeface.json', function (font) {
    loader._font = font;

    positiveSignGeometry = new TextGeometry(positiveSign, { font, size: 5, depth: 0.5 });
    negativeSignGeometry = new TextGeometry(negativeSign, { font, size: 5, depth: 0.5 });
    eSignGeometry = new TextGeometry(eSignText, { font, size: 5, depth: 0.5 });

    const textMaterial = new THREE.MeshBasicMaterial({ color: 0xffffff});
    const eTextMaterial = new THREE.MeshBasicMaterial({ color: arrowColor });

    eSignTextMesh = new THREE.Mesh(eSignGeometry, eTextMaterial);
    eSignTextMesh.position.set(-15, 3, 0);

    chargeTextMesh_pos = new THREE.Mesh(positiveSignGeometry, textMaterial);
    chargeTextMesh_pos.position.set(-43, -65, 0);

    chargeTextMesh_neg = new THREE.Mesh(negativeSignGeometry, textMaterial);
    chargeTextMesh_neg.position.set(35, -65, 0);

    scene.add(eSignTextMesh);
    scene.add(chargeTextMesh_pos);
    scene.add(chargeTextMesh_neg);
  });

  // wire paths
  const curvePath = new THREE.CurvePath();
  const points = [
    new THREE.Vector3(-75, 0, 10),
    new THREE.Vector3(-120, 0, 10),
    new THREE.Vector3(-120, -65, 10),
    new THREE.Vector3(-30, -65, 10),
  ];
  for (var i = 0; i < points.length - 1; i++) {
    curvePath.add(new THREE.LineCurve3(points[i], points[i + 1]));
  }
  const geometry = new THREE.BufferGeometry().setFromPoints(curvePath.getPoints(50));
  const material = new THREE.LineBasicMaterial({ color: 0xffffff });
  scene.add(new THREE.Line(geometry, material));

  const electronPath = new THREE.CurvePath();
  const electronPathPoints = [
    new THREE.Vector3(75, 0, 10),
    new THREE.Vector3(120, 0, 10),
    new THREE.Vector3(120, -65, 10),
    new THREE.Vector3(30, -65, 10),
  ];
  for (var i = 0; i < electronPathPoints.length - 1; i++) {
    electronPath.add(new THREE.LineCurve3(electronPathPoints[i], electronPathPoints[i + 1]));
  }
  const geometry2 = new THREE.BufferGeometry().setFromPoints(electronPath.getPoints(50));
  const material2 = new THREE.LineBasicMaterial({ color: 0xffffff });
  scene.add(new THREE.Line(geometry2, material2));

  // cube container
  const cubeGeometry = box(cubeSize.x, cubeSize.y, cubeSize.z);
  const cubeMaterial = new THREE.LineDashedMaterial({ color: 0xFFFFFF, dashSize: 3, gapSize: 1});
  cube1 = new THREE.LineSegments(cubeGeometry, cubeMaterial);
  cube1.computeLineDistances();
  cube1.position.set(0, 0, 0);

  // battery
  const batteryCylinderGeo =  new THREE.CylinderGeometry(10, 10, 60, 32);
  const wireframe = new THREE.WireframeGeometry(batteryCylinderGeo);
  const battery = new THREE.LineSegments(wireframe);
  battery.rotateZ(Math.PI/2);
  battery.material.depthTest = false;
  battery.material.opacity = 0.25;
  battery.material.transparent = true;
  battery.position.set(0, -70, 0);
  scene.add(battery);

  // plane separator
  const planeGeo = new THREE.PlaneGeometry(cubeSize.z, cubeSize.y);
  const planeMaterial = new THREE.LineDashedMaterial({ color: 0xffffff, dashSize: 3, gapSize: 1 });
  var plane = new THREE.LineSegments(planeGeo, planeMaterial);
  plane.computeLineDistances();
  plane.position.set(0, 0, 0);
  plane.rotateY(Math.PI/2);

  scene.add(cube1, plane);

  // initial spheres
  var randomVelocity;

  for (var i = 0; i < numSpheres; i++) {
    randomVelocity = SphereUtil.getBoltzVelocity(boltz);
    var holes = SphereUtil.createSphere(i, -(cubeSize.x/2) + 1, -2, holeColor, false, cubeSize);
    scene.add(holes.object);
    createIon(-(cubeSize.x/2) + 1, -2, 0xffffff, 'acceptor');

    holeSpheres.push({
      value: "h",
      initPos: holes.object.position,
      crossReady: true,
      crossed: false,
      pause: false,
      lerpProgress: 0,
      lerping: false,
      lerpPartner: new THREE.Vector3(),
      recombine: true,
      canMove: true,
      id:"normal",
      object: holes.object,
      material: holes.material,
      velocity: randomVelocity,
      speed: Math.random() * (maxScalar - minScalar + 1) + minScalar,
      scatterStartTime: performance.now(),
      scatterTime: (scatterTimeMean + (perlin.noise(i * 100, i * 200, performance.now() * 0.001) - 0.5)*0.3)
    });
  }

  for (var i = 0; i < numSpheres; i++) {
    randomVelocity = SphereUtil.getBoltzVelocity(boltz);
    createIon(2, (cubeSize.x/2) - 1, 0xffffff, 'donor');
    var electron = SphereUtil.createSphere(i, 2, (cubeSize.x/2) - 1, electronColor, false, cubeSize);
    scene.add(electron.object);

    electronSpheres.push({
      value: "e",
      initPos: electron.object.position,
      crossReady: true,
      crossed: false,
      pause: false,
      lerpProgress: 0,
      lerping: false,
      lerpPartner: new THREE.Vector3(),
      recombine: true,
      canMove: true,
      id: "normal",
      object: electron.object,
      material: electron.material,
      velocity: randomVelocity,
      speed: Math.random() * (maxScalar - minScalar + 1) + minScalar,
      scatterStartTime: performance.now(),
      scatterTime: (scatterTimeMean + (perlin.noise(i * 100, i * 200, performance.now() * 0.001) - 0.5)*0.3)
    });
  }
}


// ========================= Controller / Input Helpers =========================
function resetControllerFrameState(state) {
  state.triggerPressedLastFrame = state.triggerPressed;
  state.thumbstick.x = 0;
  state.thumbstick.y = 0;
  state.trigger = 0;
  state.triggerPressed = false;
  state.isVisionProSource = false;
}

function isVisionProInputSource(inputSource) {
  if (!inputSource) return false;

  const handedness = inputSource.handedness || '';
  if (handedness === 'none') return true;

  const profiles = inputSource.profiles || [];
  return profiles.some(profile => {
    const lowered = profile.toLowerCase();
    return lowered.includes('vision') || lowered.includes('touch') || lowered.includes('hand');
  });
}

function updateXRControllerStates(frame) {
  resetControllerFrameState(controllerStates.leftController);
  resetControllerFrameState(controllerStates.rightController);

  if (!frame) return;

  const session = frame.session;
  if (!session) return;

  session.inputSources.forEach(inputSource => {
    const gamepad = inputSource.gamepad;
    if (!gamepad) return;

    const axes = gamepad.axes || [];
    const buttons = gamepad.buttons || [];
    const visionPro = isVisionProInputSource(inputSource);
    const handedness = inputSource.handedness;
    const state = handedness === 'left' ? controllerStates.leftController : controllerStates.rightController;

    state.isVisionProSource = visionPro;
    state.inputSource = inputSource;

    let thumbX = 0;
    let thumbY = 0;

    if (axes.length >= 4 && !visionPro) {
      thumbX = axes[2] || 0;
      thumbY = axes[3] || 0;
    } else if (axes.length >= 2) {
      thumbX = axes[0] || 0;
      thumbY = axes[1] || 0;
    }

    state.thumbstick.x = thumbX;
    state.thumbstick.y = thumbY;

    if (visionPro && handedness === 'none') {
      controllerStates.leftController.thumbstick.x = thumbX;
      controllerStates.leftController.thumbstick.y = thumbY;
      controllerStates.leftController.isVisionProSource = true;
    }

    const triggerValue = buttons.length ? Math.abs((buttons[0] && buttons[0].value) || 0) : 0;
    state.trigger = triggerValue;
    state.triggerPressed = triggerValue > TRIGGER_THRESHOLD;

    // IMPORTANT: keep controller voltage changes synced through setVoltage()
    if (state.triggerPressed && !state.triggerPressedLastFrame) {
      if (state === controllerStates.rightController) {
        setVoltage(voltage + 0.08);
      } else {
        setVoltage(voltage - 0.08);
      }
    }

    state.triggerPressedLastFrame = state.triggerPressed;
  });

  controllerStates.leftController.triggerPressedLastFrame = controllerStates.leftController.triggerPressed;
  controllerStates.rightController.triggerPressedLastFrame = controllerStates.rightController.triggerPressed;
}


// ========================= Update / Animate =========================
function update() {
  renderer.setAnimationLoop(function(timestamp, frame) {
    const dt = (_lastT === null) ? 0 : (timestamp - _lastT) / 1000;
  _lastT = timestamp;

  // Desktop orbit updates only when NOT in WebXR
if (orbit && !renderer.xr.isPresenting) {
  orbit.update();
}
    updateXRControllerStates(frame);

    // wrist slider updates (pose + interaction)
    updateSliderPose(frame);
    updateSliderInteraction(frame);

    // joints + curl coloring (also tracks hands for navigation)
    if (frame && xrRefSpace_local) updateHandDebug(frame, xrRefSpace_local);

    // hand-only locomotion (disabled when Oculus controllers are present)
    applyHandGestureLocomotion(frame);
    applyThumbTurn(dt);

    const myTextEl = document.getElementById('myText');
    if (myTextEl) myTextEl.textContent = voltage.toFixed(2);

    var currentTime = performance.now();
    var time = clock.getDelta()/15;

    scene.remove(innerCube);

    innerBoxSize = 24.2*(0.58*(Math.sqrt(9.2 - voltage * 1.13 /0.05)));

    innerCubeGeometry = box(innerBoxSize, cubeSize.y, cubeSize.z);
    innerCubeMaterial = new THREE.LineDashedMaterial({ color: 0xFF0000, dashSize: 3, gapSize: 1});

    innerCube = new THREE.LineSegments(innerCubeGeometry, innerCubeMaterial);
    innerCube.computeLineDistances();
    innerCube.position.set(0, 0, 0);
    scene.add(innerCube);

    var origin = new THREE.Vector3(innerBoxSize/2, 0, 0 );
    const length = innerBoxSize;
    updateArrow(origin, length, arrowColor);

    scatter(currentTime);

    addAcceleration(electronSpheres, innerBoxSize, time, -1);
    addAcceleration(holeSpheres, innerBoxSize, time, 1);

    Generation.generationAnim(holeSpheres, electronSpheres, generatedPairs, scene, boltz);

    Recombination.updateRecombinationStatus(electronSpheres, holeSpheres, minDistance);
    Recombination.recombinationAnim(electronSpheres, holeSpheres, innerBoxSize, scene, recombination_orbs);

    if (voltage < 0) {
      sphereCrossed(electronSpheres, 'e');
      sphereCrossed(holeSpheres, 'h');
    }

    if (voltage > 0) {
      console.log("recombination count when: " + Recombination.recombinationCount);
      if (Recombination.recombinationOccured && !batteryAdded) {
        var e_position = new THREE.Vector3(cubeSize.x/2 + 50, 0, 0);
        var electron = SphereUtil.createSphereAt(e_position, electronColor, false);
        scene.add(electron.object);
        electron.value = "e";
        positiveBatteryElements.push(electron);

        var h_position = new THREE.Vector3(-cubeSize.x/2 - 50, 0, 0);
        var hole = SphereUtil.createSphereAt(h_position, holeColor, false);
        scene.add(hole.object);
        hole.value = "h";
        positiveBatteryElements.push(hole);

        Recombination.setRecombinationStatus(false);
        batteryAdded = true;
      } else {
        batteryAdded = false;
        console.log("recombination check false, has not occurred yet");
      }
    }

    if (positiveBatteryElements.length > 0) positive_battery_anim();
    if (negativeBatteryElements.length > 0) negative_battery_anim();

    updateSpherePosition();
    checkBounds(holeSpheres, electronSpheres, boxMin, boxMax);

    // controller/vision pro movement (hand gestures run separately above)
    updateCamera();

    renderer.render(scene, camera);
  });
}


// ========================= Controllers Setup =========================
function buildController(data) {
  var geometry, material;

  switch (data.targetRayMode) {
    case 'tracked-pointer':
      geometry = new THREE.BufferGeometry();
      geometry.setAttribute('position', new THREE.Float32BufferAttribute([0, 0, 0, 0, 0, -1], 3));
      geometry.setAttribute('color', new THREE.Float32BufferAttribute([0.5, 0.5, 0.5, 0, 0, 0], 3));
      material = new THREE.LineBasicMaterial({
        vertexColors: true,
        blending: THREE.AdditiveBlending
      });
      return new THREE.Line(geometry, material);

    case 'gaze':
      geometry = new THREE.RingGeometry(0.02, 0.04, 32).translate(0, 0, -1);
      material = new THREE.MeshBasicMaterial({ opacity: 0.5, transparent: true });
      return new THREE.Mesh(geometry, material);
  }
}

function setUpVRControls() {
  // Create dolly for camera movement
  dolly = new THREE.Object3D();
  dolly.position.set(0, 0, 0);
  dolly.add(camera);
  scene.add(dolly);

  // controllers
  controller1 = renderer.xr.getController(0);
  controller2 = renderer.xr.getController(1);

  controller1.addEventListener('selectstart', onSelectStart);
  controller1.addEventListener('selectend', onSelectEnd);
  controller1.addEventListener('connected', function(event) {
    this.userData.inputSource = event.data;
    this.userData.isVisionPro = isVisionProInputSource(event.data);
    const visual = buildController(event.data);
    if (visual) this.add(visual);
  });
  controller1.addEventListener('disconnected', function() {
    this.userData.inputSource = null;
    this.userData.isVisionPro = false;
    while (this.children.length) this.remove(this.children[0]);
  });

  controller2.addEventListener('selectstart', onSelectStart);
  controller2.addEventListener('selectend', onSelectEnd);
  controller2.addEventListener('connected', function(event) {
    this.userData.inputSource = event.data;
    this.userData.isVisionPro = isVisionProInputSource(event.data);
    const visual = buildController(event.data);
    if (visual) this.add(visual);
  });
  controller2.addEventListener('disconnected', function() {
    this.userData.inputSource = null;
    this.userData.isVisionPro = false;
    while (this.children.length) this.remove(this.children[0]);
  });

  // controller model
  const controllerModelFactory = new XRControllerModelFactory();

  controllerGrip1 = renderer.xr.getControllerGrip(0);
  controllerGrip2 = renderer.xr.getControllerGrip(1);

  controllerGrip1.add(controllerModelFactory.createControllerModel(controllerGrip1));
  controllerGrip2.add(controllerModelFactory.createControllerModel(controllerGrip2));

  dolly.add(controller1);
  dolly.add(controller2);
  dolly.add(controllerGrip1);
  dolly.add(controllerGrip2);
}

async function initXR(frame) {
  // keep your placeholder
}

function updateCamera() {
  if (!renderer.xr.isPresenting) return;
    // [NAV TOGGLE]
  if (!navigationEnabled) return;


  const leftThumbstick = controllerStates.leftController.thumbstick;
  const rightThumbstick = controllerStates.rightController.thumbstick;

  let moveX = leftThumbstick.x;
  let moveY = leftThumbstick.y;

  // Mirror Vision Pro axes if only right controller reports them
  if (Math.abs(moveX) <= 0.01 && Math.abs(moveY) <= 0.01 && controllerStates.rightController.isVisionProSource) {
    moveX = rightThumbstick.x;
    moveY = rightThumbstick.y;
  }

  // For Vision Pro, use trackpad Y to move and ignore strafing for comfort
  if (controllerStates.leftController.isVisionProSource) {
    moveX = 0;
  }

  if (Math.abs(moveX) > 0.1 || Math.abs(moveY) > 0.1) {
    const forward = new THREE.Vector3();
    camera.getWorldDirection(forward);
    forward.y = 0;
    if (forward.lengthSq() > 0) {
      forward.normalize();
      const right = new THREE.Vector3().crossVectors(WORLD_UP, forward).normalize();

      const moveVector = new THREE.Vector3();
      moveVector.addScaledVector(forward, -moveY * vrSettings.moveSpeed);
      moveVector.addScaledVector(right, moveX * vrSettings.moveSpeed);
      dolly.position.add(moveVector);
    }
  }

  let rotationInput = rightThumbstick.x;

  if (controllerStates.rightController.isVisionProSource) {
    rotationInput = rightThumbstick.x;
  }

  if (Math.abs(rotationInput) > 0.1) {
    dolly.rotation.y -= rotationInput * vrSettings.rotationSpeed;
  }

  applyVisionProSelectMovement();
}

function applyVisionProSelectMovement() {
    // [NAV TOGGLE]
  if (!navigationEnabled) return;

  const visionProActive = controllerStates.leftController.isVisionProSource || controllerStates.rightController.isVisionProSource;
  if (!visionProActive) return;

  const axesThreshold = 0.08;
  const hasActiveAxes = (Math.abs(controllerStates.leftController.thumbstick.x) > axesThreshold ||
    Math.abs(controllerStates.leftController.thumbstick.y) > axesThreshold ||
    Math.abs(controllerStates.rightController.thumbstick.x) > axesThreshold ||
    Math.abs(controllerStates.rightController.thumbstick.y) > axesThreshold);

  const controllersArray = [controller1, controller2];
  controllersArray.forEach(controller => {
    if (!controller || !controller.userData || !controller.userData.isSelecting) return;

    const inputSource = controller.userData.inputSource;
    if (!isVisionProInputSource(inputSource)) return;

    if (hasActiveAxes) return;

    const direction = new THREE.Vector3();
    controller.getWorldDirection(direction);
    direction.negate();
    direction.y = 0;
    if (direction.lengthSq() < 1e-6) return;

    direction.normalize();
    dolly.position.addScaledVector(direction, vrSettings.moveSpeed * 0.5);
  });
}

function onSelectStart() { this.userData.isSelecting = true; }
function onSelectEnd() { this.userData.isSelecting = false; }


// ========================= Your Existing Simulation Functions (unchanged) =========================
function negative_battery_anim() {
  for (var i = negativeBatteryElements.length - 1; i >= 0; i--) {
    var sphere = negativeBatteryElements[i];
    var spherePosition = sphere.object.position;

    if (sphere.value == 'e') {
      if (spherePosition.x <= cubeSize.x/2) {
        sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));
      } else {
        sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));
        sphere.object.material.transparent = true;

        var distanceFromEdge = Math.abs(sphere.object.position.x - cubeSize.x/2);
        var maxDistance = 50;
        var opacity = THREE.MathUtils.clamp(1 - (distanceFromEdge / maxDistance), 0, 1);

        sphere.object.material.opacity = opacity;

        if (opacity <= 0) {
          scene.remove(sphere.object);
          negativeBatteryElements.splice(i, 1);
        }
      }
    } else if (sphere.value == 'h') {
      if (spherePosition.x >= -cubeSize.x/2) {
        sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));
      } else {
        sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));
        sphere.object.material.transparent = true;

        var distanceFromEdge = Math.abs(sphere.object.position.x + cubeSize.x/2);
        var maxDistance = 50;
        var opacity = THREE.MathUtils.clamp(1 - (distanceFromEdge / maxDistance), 0, 1);

        sphere.object.material.opacity = opacity;

        if (opacity <= 0) {
          scene.remove(sphere.object);
          negativeBatteryElements.splice(i, 1);
        }
      }
    }
  }
}

function positive_battery_anim() {
  console.log("length of postiive battery elements array:" + positiveBatteryElements.length);

  for (var i = positiveBatteryElements.length - 1; i >= 0; i--) {
    var sphere = positiveBatteryElements[i];
    var spherePosition = sphere.object.position;

    if (sphere.value == 'e') {
      if (spherePosition.x < cubeSize.x/2 - 1) {
        electronSpheres.push({
          value: "e",
          crossReady: true,
          crossed: false,
          pause: false,
          lerpProgress: 0,
          lerping: false,
          lerpPartner: new THREE.Vector3(),
          recombine: true,
          id: "generated",
          canMove: true,
          object: sphere.object,
          material: sphere.material,
          velocity: SphereUtil.getBoltzVelocity(boltz),
          speed: Math.random() * (maxScalar - minScalar + 1) + minScalar,
          scatterStartTime: performance.now(),
          scatterTime: (scatterTimeMean + (perlin.noise(Math.random(0, numSpheres) * 100, Math.random(0, numSpheres) * 200, performance.now() * 0.001) - 0.5)*0.3)
        });
        positiveBatteryElements.splice(i, 1);
      } else {
        sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));
      }
    } else if (sphere.value == 'h') {
      if (spherePosition.x > -cubeSize.x/2 + 1) {
        holeSpheres.push({
          value: "h",
          crossReady: true,
          crossed: false,
          pause: false,
          lerpProgress: 0,
          lerping: false,
          lerpPartner: new THREE.Vector3(),
          recombine: true,
          id: 'generated',
          canMove: true,
          object: sphere.object,
          material: sphere.material,
          velocity: SphereUtil.getBoltzVelocity(boltz),
          speed: Math.random() * (maxScalar - minScalar + 1) + minScalar,
          scatterStartTime: performance.now(),
          scatterTime: (scatterTimeMean + (perlin.noise(Math.random(0, numSpheres) * 100, Math.random(0, numSpheres) * 200, performance.now() * 0.001) - 0.5)*0.3)
        });
        positiveBatteryElements.splice(i, 1);
      } else {
        sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));
      }
    }
  }
}

function sphereCrossed(typeArray, type) {
  var e_count = 0;
  var h_count = 0;

  if (!voltageChangedOnce) voltageChangedOnce = true;

  for (var i = 0; i < typeArray.length; i++) {
    var spherePosition = typeArray[i].object.position.x;

    if (voltage < 0) {
      if (type == 'e') {
        if (spherePosition > innerBoxSize/2) {
          e_count= e_count+1;
          if (e_count > numSpheres) {
            e_count= e_count-1;
            var position = new THREE.Vector3(cubeSize.x/2 - 5, 0, 0);
            var electron = SphereUtil.createSphereAt(position, electronColor, false);
            scene.add(electron.object);
            electron.value = "e";

            typeArray[i].crossed = true;
            negativeBatteryElements.push(electron);

            var randomIndex = Math.floor(Math.random() * electronSpheres.length);
            scene.remove(electronSpheres[randomIndex].object);
            electronSpheres[randomIndex].object.geometry.dispose();
            electronSpheres[randomIndex].object.material.dispose();
            electronSpheres.splice(randomIndex, 1);
          }
        }
      } else if (type == 'h') {
        if (spherePosition < -innerBoxSize/2 ) {
          h_count= h_count+1;
          if (h_count > numSpheres ) {
            h_count= h_count-1;
            var position = new THREE.Vector3(-cubeSize.x/2 + 5, 0, 0);
            var hole = SphereUtil.createSphereAt(position, holeColor, false);
            scene.add(hole.object);
            hole.value = "h";
            typeArray[i].crossed = true;
            negativeBatteryElements.push(hole);

            var randomIndex = Math.floor(Math.random() * holeSpheres.length);
            scene.remove(holeSpheres[randomIndex].object);
            holeSpheres[randomIndex].object.geometry.dispose();
            holeSpheres[randomIndex].object.material.dispose();
            holeSpheres.splice(randomIndex, 1);
          }
        }
      }
    }

    if (voltage === 0 ) {
      if (type == 'e') {
        if (spherePosition > innerBoxSize/2) {
          e_count= e_count+1;
          if (e_count > numSpheres ) {
            e_count= e_count-1;
            var randomIndex = Math.floor(Math.random() * electronSpheres.length);
            scene.remove(electronSpheres[randomIndex].object);
            electronSpheres[randomIndex].object.geometry.dispose();
            electronSpheres[randomIndex].object.material.dispose();
            electronSpheres.splice(randomIndex, 1);
          }
        }
      } else if (type == 'h') {
        if (spherePosition < -innerBoxSize/2 ) {
          h_count= h_count+1;
          if (h_count > numSpheres ) {
            h_count= h_count-1;
            var randomIndex = Math.floor(Math.random() * holeSpheres.length);
            scene.remove(holeSpheres[randomIndex].object);
            holeSpheres[randomIndex].object.geometry.dispose();
            holeSpheres[randomIndex].object.material.dispose();
            holeSpheres.splice(randomIndex, 1);
          }
        }
      }
    }
  }
}

function addAcceleration(type, innerBoxSize, time, scalar) {
  for (var i = 0; i < type.length; i++) {
    var spherePosition = type[i].object.position.x;
    var acc = new THREE.Vector3(0, 0, 0);

    if ((-innerBoxSize/2 < spherePosition && spherePosition < 0)) {
      acc = new THREE.Vector3(-1.53*(innerBoxSize/2 + spherePosition), 0 , 0);
    }
    if ((0 < spherePosition && spherePosition < innerBoxSize/2)) {
      acc = new THREE.Vector3(-1.53*(innerBoxSize/2 - spherePosition), 0, 0);
    }
    if ((-cubeSize.x/2 + 1 < spherePosition && spherePosition < -innerBoxSize/2) ||
        (innerBoxSize/2 < spherePosition && spherePosition < cubeSize.x/2 - 1) ||
        (spherePosition == 0)) {
      acc = new THREE.Vector3(0, 0, 0);
    }

    if (scalar < 0) {
      electronSpheres[i].velocity.add(acc.multiplyScalar(time).multiplyScalar(scalar));
    } else {
      holeSpheres[i].velocity.add(acc.multiplyScalar(time));
    }
  }
}

function updateSpherePosition() {
  const minVelocity = 0.000001;
  const maxVelocity = 30;
  for (var sphere of [...electronSpheres, ...holeSpheres]) {
    const currVelocity = sphere.velocity.clone();
    currVelocity.clampLength(minVelocity, maxVelocity);
    if (sphere.canMove == true) {
      sphere.object.position.add(currVelocity);
      sphere.velocity = currVelocity;
    }
  }
}

function scatter(currentTime) {
  for (var i = 0; i < electronSpheres.length; i++) {
    for (var j = 0; j < holeSpheres.length; j++) {
      var electronScatterTime = (currentTime - electronSpheres[i].scatterStartTime)/1000;
      if (electronScatterTime >= electronSpheres[i].scatterTime) {
        electronSpheres[i].velocity = SphereUtil.getBoltzVelocity(boltz);
        electronSpheres[i].scatterStartTime = performance.now();
        electronSpheres[i].scatterTime = (scatterTimeMean + (perlin.noise(i * 100, i * 200, performance.now() * 0.001) - 0.5)*0.3);
      }

      var holeScatterTime = (currentTime - holeSpheres[j].scatterStartTime)/1000;
      if (holeScatterTime >= holeSpheres[j].scatterTime) {
        holeSpheres[j].velocity = SphereUtil.getBoltzVelocity(boltz);
        holeSpheres[j].scatterStartTime = performance.now();
        holeSpheres[j].scatterTime = (scatterTimeMean + (perlin.noise(j * 100, j * 200, performance.now() * 0.001) - 0.5)*0.3);
      }
    }
  }
}

function checkBounds(sphere1, sphere2, min, max) {
  var yedge = (cubeSize.y/2);
  var ynedge = -(yedge);
  var zedge = (cubeSize.z/2);
  var znedge = -(zedge);

  for (var i = 0; i < sphere1.length; i++) {
    if (sphere1[i].object.position.x >= max) {
      sphere1[i].object.position.x = min + 1;
    } else if (sphere1[i].object.position.x <= min) {
      sphere1[i].object.position.x = THREE.MathUtils.randFloat(min + 1, min + 20);
    }
    if (sphere1[i].object.position.y > yedge) {
      sphere1[i].object.position.y = yedge - 1;
      sphere1[i].velocity.multiplyScalar(-1);
    } else if (sphere1[i].object.position.y < ynedge) {
      sphere1[i].object.position.y = ynedge + 1;
      sphere1[i].velocity.multiplyScalar(-1);
    }
    if (sphere1[i].object.position.z > zedge) {
      sphere1[i].object.position.z = zedge - 1;
      sphere1[i].velocity.multiplyScalar(-1);
    } else if (sphere1[i].object.position.z < znedge) {
      sphere1[i].object.position.z = znedge + 1;
      sphere1[i].velocity.multiplyScalar(-1);
    }
  }

  for (var i = 0; i < sphere2.length; i++) {
    if (sphere2[i].object.position.x >= max) {
      sphere2[i].object.position.x = THREE.MathUtils.randFloat(max - 15 , max - 1);
    } else if (sphere2[i].object.position.x <= min) {
      sphere2[i].object.position.x = max - 1;
    }

    if (sphere2[i].object.position.y > yedge) {
      sphere2[i].object.position.y = yedge - 1;
      sphere2[i].velocity.multiplyScalar(-1);
    } else if (sphere2[i].object.position.y < ynedge) {
      sphere2[i].object.position.y = ynedge + 1;
      sphere2[i].velocity.multiplyScalar(-1);
    }

    if (sphere2[i].object.position.z > zedge) {
      sphere2[i].object.position.z = zedge - 1;
      sphere2[i].velocity.multiplyScalar(-1);
    } else if (sphere2[i].object.position.z < znedge) {
      sphere2[i].object.position.z = znedge + 1;
      sphere2[i].velocity.multiplyScalar(-1);
    }
  }
}

function resetGUI() {
  gui.__controllers.forEach(controller => controller.setValue(controller.initialValue));
}

function createIon(minx, maxx, color, ionType) {
  var capsuleLength = 3;
  var radius = 0.5;
  const geometry = new THREE.CapsuleGeometry(radius, capsuleLength);

  if (ionType == "acceptor") {
    var material = new THREE.MeshBasicMaterial({color: color, transparent: true, opacity: 0.2});
    var acceptor = new THREE.Mesh(geometry, material);
    acceptor.rotateZ(Math.PI/2);
    acceptor.position.set(
      THREE.MathUtils.randFloat(minx, maxx),
      THREE.MathUtils.randFloat(-cubeSize.y/2 + 1, cubeSize.y/2 - 1),
      THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1)
    );
    scene.add(acceptor);
  } else if (ionType == 'donor') {
    var geometry2 = new THREE.CapsuleGeometry(radius, capsuleLength);
    geometry2.rotateZ(Math.PI/2);
    var mergedGeometry = new BufferGeometryUtils.mergeGeometries([geometry, geometry2]);
    var material = new THREE.MeshBasicMaterial({color: color, transparent: true,  opacity: 0.2});
    var donor = new THREE.Mesh(mergedGeometry, material);
    donor.position.set(
      THREE.MathUtils.randFloat(minx, maxx),
      THREE.MathUtils.randFloat(-cubeSize.y/2 + 1, cubeSize.y/2 - 1),
      THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1)
    );
    scene.add(donor);
  }
}

function updateArrow(origin, length, hex) {
  var headLength = innerBoxSize/4;
  scene.remove(arrowNegative);
  arrowNegative = new THREE.ArrowHelper(new THREE.Vector3(-1, 0, 0), origin, length, hex, headLength);
  scene.add(arrowNegative);
}

function box(width, height, depth) {
  width = width * 0.5;
  height = height * 0.5;
  depth = depth * 0.5;

  const geometry = new THREE.BufferGeometry();
  const position = [];

  position.push(
    - width, - height, - depth,
    - width, height, - depth,

    - width, height, - depth,
    width, height, - depth,

    width, height, - depth,
    width, - height, - depth,

    width, - height, - depth,
    - width, - height, - depth,

    - width, - height, depth,
    - width, height, depth,

    - width, height, depth,
    width, height, depth,

    width, height, depth,
    width, - height, depth,

    width, - height, depth,
    - width, - height, depth,

    - width, - height, - depth,
    - width, - height, depth,

    - width, height, - depth,
    - width, height, depth,

    width, height, - depth,
    width, height, depth,

    width, - height, - depth,
    width, - height, depth
  );

  geometry.setAttribute('position', new THREE.Float32BufferAttribute(position, 3));
  return geometry;
}

function onWindowResize() {
  camera.aspect = container.clientWidth / container.clientHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(container.clientWidth, container.clientHeight, false);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
}
