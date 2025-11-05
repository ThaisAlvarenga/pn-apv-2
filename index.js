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

const hdrFile = "./assets/black.hdr";
//scene set up variables and window variables

var container, camera, renderer;
var voltageLevel;
var cameraControls;
var gui;
const voltageControl = document.getElementById('voltage');
var minScalar = 0.22;
var maxScalar = 0.88;
var cube1;
var holeColor = 0xd55e00
var electronColor = 0x56b4e9;



//PN Junction Initial Variables
var electronSpheres = [];
var holeSpheres = [];
var numSpheres = 50;

var cubeSize = new THREE.Vector3(150, 75, 75);
var clock = new THREE.Clock();

var boxMin = -(cubeSize.x/2) + 1;
var boxMax = (cubeSize.x/2) - 1;


//electric field attributes
var arrowNegative;
var innerBoxSize = 25;
var innerCubeGeometry;
var innerCubeMaterial;
var innerCube;
var voltage = 0.0;
const arrowColor = 0xf0e442;

//text components in 3d scene
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


//scatter variables
var scatterTimeMean = 2;
const perlin = new ImprovedNoise();

//battery variables
var positiveBatteryElements = [];
var negativeBatteryElements = [];
let batteryAdded = false; // Global flag

let voltageChangedOnce = false;

// populate boltz distribution table
var boltz = []; 

//recombination variables
var minDistance = 30;
var e_sphere_outside_depvarion_range = false;
var h_sphere_outside_depvarion_range = false;
var recombination_orbs = [];

//generation variables
var generatedPairs = []; //[{electron, hole}, {electron, hole}]


//VR control variables
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


//movement settings
const vrSettings = {
	moveSpeed: 2,
	rotationSpeed: 0.05
};

const loader = new FontLoader();
var scene = new THREE.Scene();


// ========================= Wrist Slider (left wrist, right-hand ray) =========================

// CONFIG
const SL_MIN = -1.4;
const SL_MAX =  0.4;
const SL_TRACK_M = 0.18; // 18 cm

// Scene nodes
const ws = {
  root: new THREE.Object3D(),  // follows left wrist / left grip
  tilt: new THREE.Object3D(),  // reserved (extra tilt)
  panel: new THREE.Object3D(), // UI container
  track: null,
  knob: null,
  labelMesh: null,
  labelTex: null,
};

// State
let ws_value = 0.0;                     // current slider value (volts)
let ws_dragging = false;                // dragging with right select?
let ws_dragController = null;           // which controller is dragging
let ws_refSpace = null;                 // 'local-floor'
let ws_leftHand = null;                 // XRInputSource for left hand (if any)
let ws_rightController = null;          // THREE.Object3D for right controller (ray origin)
const ws_ray = new THREE.Raycaster();   // raycaster for hover/drag
const _tmpMat = new THREE.Matrix4();

// helpers for mapping value <-> x along track
const v2x = (v) => THREE.MathUtils.mapLinear(v, SL_MIN, SL_MAX, -SL_TRACK_M/2, SL_TRACK_M/2);
const x2v = (x) => THREE.MathUtils.clamp(
  THREE.MathUtils.mapLinear(x, -SL_TRACK_M/2, SL_TRACK_M/2, SL_MIN, SL_MAX),
  SL_MIN, SL_MAX
);

// public accessors (optional)
function getVoltageFromWristSlider() { return ws_value; }
function setVoltageOnWristSlider(v) {
  ws_value = THREE.MathUtils.clamp(v, SL_MIN, SL_MAX);
  if (ws.knob) ws.knob.position.x = v2x(ws_value);
  drawVoltageLabel(ws_value);
}

// build UI pieces
function buildWristSliderUI() {
  // panel root
  scene.add(ws.root);
  ws.root.add(ws.tilt);
  ws.tilt.add(ws.panel);

  // background
  const bg = new THREE.Mesh(
    new THREE.PlaneGeometry(0.22, 0.10),
    new THREE.MeshBasicMaterial({ color: 0x000000, transparent: true, opacity: 0.45 })
  );
  bg.position.z = -0.001;
  ws.panel.add(bg);

  // track
  ws.track = new THREE.Mesh(
    new THREE.PlaneGeometry(SL_TRACK_M, 0.02),
    new THREE.MeshBasicMaterial({ color: 0x222222, transparent: true, opacity: 0.85 })
  );
  ws.panel.add(ws.track);

  // knob
  ws.knob = new THREE.Mesh(
    new THREE.CircleGeometry(0.015, 32),
    new THREE.MeshBasicMaterial({ color: 0xffcc66 })
  );
  ws.knob.position.z = 0.001;
  ws.panel.add(ws.knob);

  // label (canvas)
  const cvs = document.createElement('canvas');
  cvs.width = 1024; cvs.height = 256;
  ws.labelTex = new THREE.CanvasTexture(cvs);
  ws.labelTex.colorSpace = THREE.SRGBColorSpace;
  ws.labelTex.minFilter = THREE.LinearFilter;
  ws.labelTex.magFilter = THREE.LinearFilter;

  ws.labelMesh = new THREE.Mesh(
    new THREE.PlaneGeometry(0.30, 0.09),
    new THREE.MeshBasicMaterial({
      map: ws.labelTex,
      transparent: true,
      depthTest: false,
      depthWrite: false
    })
  );
  ws.labelMesh.position.set(0, 0.09, 0.006);
  ws.panel.add(ws.labelMesh);
  ws.labelCanvas = cvs;
  ws.labelCtx = cvs.getContext('2d');

  // local placement & tilt (so it’s easy to see on wrist)
  ws.panel.position.set(0.07, 0.02, -0.05);
  ws.panel.rotation.set(
    THREE.MathUtils.degToRad(45),  // tilt up
    THREE.MathUtils.degToRad(25),  // yaw toward user’s right
    THREE.MathUtils.degToRad(-90)  // flat on forearm
  );

  // init visuals
  ws.knob.position.x = v2x(ws_value);
  drawVoltageLabel(ws_value);
}

function drawVoltageLabel(v) {
  if (!ws.labelCtx) return;
  const ctx = ws.labelCtx;
  const W = ws.labelCanvas.width, H = ws.labelCanvas.height;
  ctx.clearRect(0,0,W,H);
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  ctx.fillRect(0,0,W,H);
  ctx.fillStyle = '#ffffff';
  ctx.font = 'bold 120px system-ui, -apple-system, Segoe UI, Roboto, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText(`Voltage: ${v.toFixed(2)} V`, W/2, H/2);
  ws.labelTex.needsUpdate = true;
}

// pose the slider root at left wrist (fallback: left controller grip(0))
function updateLeftWristPose(frame) {
  const session = renderer.xr.getSession?.();
  if (!session || !ws_refSpace) { ws.root.visible = false; return; }

  // Try left hand
  if (!ws_leftHand) {
    for (const src of session.inputSources) {
      if (src.hand && src.handedness === 'left') { ws_leftHand = src; break; }
    }
  }
  if (ws_leftHand && ws_leftHand.hand) {
    const ht = ws_leftHand.hand;
    const wrist = ht.get?.('wrist') || (typeof XRHand!=='undefined' && ht[XRHand.WRIST]);
    if (wrist) {
      const pose = frame.getJointPose(wrist, ws_refSpace);
      if (pose) {
        const t = pose.transform;
        ws.root.position.set(t.position.x, t.position.y, t.position.z);
        ws.root.quaternion.set(t.orientation.x, t.orientation.y, t.orientation.z, t.orientation.w);
        ws.root.visible = true;
        return;
      }
    }
  }

  // Fallback: left controller grip(0)
  const grip0 = renderer.xr.getControllerGrip?.(0);
  if (grip0) {
    grip0.matrixWorld.decompose(ws.root.position, ws.root.quaternion, ws.root.scale);
    ws.root.visible = true;
    return;
  }

  ws.root.visible = false;
}

// helper: raycast from a controller into knob/track
function intersectSlider(ctrlObj) {
  _tmpMat.identity().extractRotation(ctrlObj.matrixWorld);
  ws_ray.ray.origin.setFromMatrixPosition(ctrlObj.matrixWorld);
  ws_ray.ray.direction.set(0,0,-1).applyMatrix4(_tmpMat);

  const hits = ws_ray.intersectObjects([ws.knob, ws.track], false);
  return hits.length ? hits[0] : null;
}

// Right-hand “select” starts dragging only if we’re pointing at the slider
function onRightSelectStart(e) {
  const ctrlObj = e.target; // THREE.Object3D for this controller
  if (ctrlObj !== ws_rightController) return; // only right-hand

  const hit = intersectSlider(ctrlObj);
  if (hit) {
    ws_dragging = true;
    ws_dragController = ctrlObj;
  }
}
function onRightSelectEnd(e) {
  if (e.target === ws_dragController) {
    ws_dragging = false;
    ws_dragController = null;
  }
}

// while dragging: project controller’s ray hit to local panel X and convert to value
function updateDrag() {
  if (!ws_dragging || !ws_dragController) return;
  const hit = intersectSlider(ws_dragController);
  if (!hit) return;

  const local = ws.panel.worldToLocal(hit.point.clone());
  const clampedX = THREE.MathUtils.clamp(local.x, -SL_TRACK_M/2, SL_TRACK_M/2);

  ws_value = x2v(clampedX);
  ws.knob.position.x = THREE.MathUtils.lerp(ws.knob.position.x, clampedX, 0.45);
  drawVoltageLabel(ws_value);
}

// PUBLIC API to init and tick
function initWristSlider() {
  buildWristSliderUI();

  // XR session setup
  renderer.xr.addEventListener('sessionstart', async () => {
    const s = renderer.xr.getSession();
    ws_refSpace = await s.requestReferenceSpace('local-floor');

    // discover right controller object for ray origin
    ws_rightController = renderer.xr.getController?.(1); // index 1 = right (typical)
    if (ws_rightController) {
      ws_rightController.addEventListener('selectstart', onRightSelectStart);
      ws_rightController.addEventListener('selectend',   onRightSelectEnd);
    }

    s.addEventListener('inputsourceschange', () => {
      ws_leftHand = null; // force re-scan next frame
    });
  });

  renderer.xr.addEventListener('sessionend', () => {
    ws_refSpace = null;
    ws_leftHand = null;
    ws_dragging = false;
    ws_dragController = null;
  });
}

function tickWristSlider(frame) {
  // follow wrist/grip
  updateLeftWristPose(frame);

  // controller drag
  updateDrag();

  // hand-tracking pinch (optional): skip per your spec (right-hand click only)
  // If you later want pinch, it can be added here.
}


init();

update();

setInterval(() => {
    let generatedPair = Generation.generatePair(cubeSize);
    scene.add(generatedPair.orbSphere);
    scene.add(generatedPair.electron.object);
    scene.add(generatedPair.hole.object);
    generatedPairs.push(generatedPair);
}, 2000);


setInterval(() => {
    let generatedPair = Generation.generatePair(cubeSize);
    scene.add(generatedPair.orbSphere);
    scene.add(generatedPair.electron.object);
    scene.add(generatedPair.hole.object);
    generatedPairs.push(generatedPair);
}, 2000);

//RECOMBINATION ORB CLEAN UP
setInterval(() => {
    //creates hole/electron pair and adds to generatedPairs array
    Recombination.recombinationOrbRemove(recombination_orbs, scene);
}, 2000);

 
function init() {
    //camera, background textures, background, scene, initial geometry, materials, renderer
    const norm_vel = [{nv: 0.1, quantity: 3}, {nv: 0.2, quantity: 10}, {nv: 0.3, quantity: 21}, {nv: 0.4, quantity: 35}, {nv: 0.5, quantity: 49}, 
        {nv: 0.6, quantity: 63}, {nv: 0.7, quantity: 74}, {nv: 0.8, quantity: 82}, {nv: 0.9, quantity: 86}, {nv: 1.0, quantity: 86},
        {nv: 1.1, quantity: 83}, {nv: 1.2, quantity: 77}, {nv: 1.3, quantity: 69}, {nv: 1.4, quantity: 59}, {nv: 1.5, quantity: 50}, {nv: 1.6, quantity: 40},
        {nv: 1.7, quantity: 32}, {nv: 1.8, quantity: 24}, {nv: 1.9, quantity: 18}, {nv: 3.0, quantity: 13}, {nv: 2.1, quantity: 9}, {nv: 2.2, quantity: 6}, {nv: 2.3, quantity: 4},
        {nv: 3.5, quantity: 3}, {nv: 4, quantity: 2}, {nv: 5, quantity: 1}, {nv: 6, quantity: 1}];
    for (var i = 0; i < norm_vel.length; i++) {
        var count = 0;
        while (count < norm_vel[i].quantity) {
            boltz.push(norm_vel[i].nv);
            count++;
        }
    }
    
    container = document.getElementById('three-container-scene-1');
   
    new RGBELoader()
    .load(hdrFile, function (texture) {
        scene.background = texture;  // This makes HDR the background
        scene.environment = texture; // This applies HDR for lighting/reflection        
    }, undefined, function (error) {
        console.error("Failed to load HDR file:", error);
    })

    //camera
    camera = new THREE.PerspectiveCamera( 75, container.clientWidth / container.clientHeight, 0.1, 1500);
    // camera.position.z = 150;
    camera.position.set(0, 0, 150);
    //renderer
    renderer = new THREE.WebGLRenderer({ alpha: false });

    renderer.setSize(container.clientWidth, container.clientHeight);
    renderer.xr.enabled = true;
    renderer.xr.setReferenceSpaceType('local-floor');
    initXR();
    container.appendChild( renderer.domElement );
	container.appendChild(XRButton.createButton(renderer));
	dolly = new THREE.Object3D();
	setUpVRControls();

    initWristSlider();


     // Add explicit size check
     if (!container) {
        console.error('Container not found');
        return;
    }
	
		
	//lighting
    // const light = new THREE.AmbientLight( 0xffffff, 3); // soft white light
    // scene.add( light );

    const light = new THREE.AmbientLight( 0xffffff, 1 );  // softer light
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

    voltageLevel = {
        x: 0.0,
    };

    document.getElementById("myText").innerHTML = 0;

    // moved to update

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

    gui.add(thermalControls, 'scalar', 0.001, 1.5, 0.01)
    .name('Sphere Scalar')
    .onChange((v) => {
        SphereUtil.setScalar(v);
    });


    const resetButton = { 'Reset Cube': resetGUI };

    // Add a button to reset GUI controls
    gui.add(resetButton, 'Reset Cube');

    
    container.appendChild(gui.domElement);


    voltageControl.addEventListener('input', () => {
        voltageLevel = parseFloat(voltageControl.value);
        voltage = voltageLevel;
        document.getElementById("myText").innerHTML = voltage;
     });

 
    

    // window resize handler
    window.addEventListener( 'resize', onWindowResize);

    loader.load( 'https://unpkg.com/three@0.163.0/examples/fonts/helvetiker_regular.typeface.json', function ( font ) {
        loader._font = font;
        positiveSignGeometry = new TextGeometry( positiveSign, {
            font: font,
            size: 5,
            depth: 0.5
        } );
        negativeSignGeometry = new TextGeometry( negativeSign, {
            font: font,
            size: 5,
            depth: 0.5
        } );
        eSignGeometry = new TextGeometry(eSignText, {
            font: font,
            size: 5,
            depth: 0.5
        });

        const textMaterial = new THREE.MeshBasicMaterial({ color: 0xffffff});
        const eTextMaterial = new THREE.MeshBasicMaterial({color: arrowColor})

        eSignTextMesh = new THREE.Mesh(eSignGeometry, eTextMaterial);
        eSignTextMesh.position.set(-15, 3, 0); //position E text on top of the charge arrow

        chargeTextMesh_pos = new THREE.Mesh(positiveSignGeometry, textMaterial);
        chargeTextMesh_pos.position.set(-43, -65, 0); // Position positive sign on left side of battery

        chargeTextMesh_neg = new THREE.Mesh(negativeSignGeometry, textMaterial);
        chargeTextMesh_neg.position.set(35, -65, 0); //position negative sign on right side of battery

        scene.add(eSignTextMesh);
        scene.add(chargeTextMesh_pos);
        scene.add(chargeTextMesh_neg);
    
    } );

   

    // Create an angular path
    const curvePath = new THREE.CurvePath();

    // Define the points for our angular path
    const points = [
    new THREE.Vector3(-75, 0, 10),
    new THREE.Vector3(-120, 0, 10),
    new THREE.Vector3(-120, -65, 10),
    new THREE.Vector3(-30, -65, 10),

   
    ];

    // Create line segments between each pair of points
    for (var i = 0; i < points.length - 1; i++) {
    const lineCurve = new THREE.LineCurve3(points[i], points[i + 1]);
    curvePath.add(lineCurve);
    }

    // Create a visible path for reference
    const geometry = new THREE.BufferGeometry().setFromPoints(curvePath.getPoints(50));
    const material = new THREE.LineBasicMaterial({ color: 0xffffff });
    const visiblePath = new THREE.Line(geometry, material);
    scene.add(visiblePath);

    //ELECTRON WIRE
    // Create an angular path
    const electronPath = new THREE.CurvePath();

    // Define the points for our angular path
    const electronPathPoints = [
    new THREE.Vector3(75, 0, 10),
    new THREE.Vector3(120, 0, 10),
    new THREE.Vector3(120, -65, 10),
    new THREE.Vector3(30, -65, 10),

    
    ];

    // Create line segments between each angular path points
    for (var i = 0; i < electronPathPoints.length - 1; i++) {
    const lineCurve = new THREE.LineCurve3(electronPathPoints[i], electronPathPoints[i + 1]);
    electronPath.add(lineCurve);
    }

    // Create a visible path
    const geometry2 = new THREE.BufferGeometry().setFromPoints(electronPath.getPoints(50));
    const material2 = new THREE.LineBasicMaterial({ color: 0xffffff });
    const visiblePath2 = new THREE.Line(geometry2, material2);
    scene.add(visiblePath2);

    // create cube container
    const cubeGeometry = box(cubeSize.x, cubeSize.y, cubeSize.z);
    const cubeMaterial = new THREE.LineDashedMaterial({ color: 0xFFFFFF, dashSize: 3, gapSize: 1});
    cube1 = new THREE.LineSegments(cubeGeometry, cubeMaterial);
    cube1.computeLineDistances();
    cube1.position.set(0, 0, 0);

    //battery geometry
    const batteryCylinderGeo =  new THREE.CylinderGeometry( 10, 10, 60, 32 );
    const wireframe = new THREE.WireframeGeometry( batteryCylinderGeo );

    const battery = new THREE.LineSegments( wireframe );
    battery.rotateZ(Math.PI/2);

    battery.material.depthTest = false;
    battery.material.opacity = 0.25;
    battery.material.transparent = true;
    battery.position.set(0, -70, 0);

    scene.add( battery );

    // create a plane in the middle to separate P type and N type
    const planeGeo = new THREE.PlaneGeometry(cubeSize.z, cubeSize.y);
    const planeMaterial = new THREE.LineDashedMaterial({
        color: 0xffffff,
        dashSize: 3,
        gapSize: 1,
    });
    // const planeMaterial = new THREE.MeshBasicMaterial( {color: 0xFFFFFF, side: THREE.DoubleSide, transparent: true} );
    var plane = new THREE.LineSegments(planeGeo, planeMaterial);
    plane.computeLineDistances();
    plane.position.set(0, 0, 0);
    plane.rotateY(Math.PI/2);

    scene.add(cube1, plane);

    var randomVelocity;
    //create initial holes and acceptors
    for (var i = 0; i < numSpheres; i++) {
        // change this to boltzmann distributed velocity
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

    //create initial electrons and donors
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
            scatterTime: (scatterTimeMean + (perlin.noise(i * 100, i * 200, performance.now() * 0.001) - 0.5)*0.3)});
    }

}

function resetControllerFrameState(state) {
	state.triggerPressedLastFrame = state.triggerPressed;
	state.thumbstick.x = 0;
	state.thumbstick.y = 0;
	state.trigger = 0;
	state.triggerPressed = false;
	state.isVisionProSource = false;
}

function isVisionProInputSource(inputSource) {
	if (!inputSource) {
		return false;
	}

	const handedness = inputSource.handedness || '';
	if (handedness === 'none') {
		return true;
	}

	const profiles = inputSource.profiles || [];
	return profiles.some(profile => {
		const lowered = profile.toLowerCase();
		return lowered.includes('vision') || lowered.includes('touch') || lowered.includes('hand');
	});
}

function updateXRControllerStates(frame) {
	resetControllerFrameState(controllerStates.leftController);
	resetControllerFrameState(controllerStates.rightController);

	if (!frame) {
		return;
	}

	const session = frame.session;
	if (!session) {
		return;
	}

	session.inputSources.forEach(inputSource => {
		const gamepad = inputSource.gamepad;
		if (!gamepad) {
			return;
		}

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

		if (state.triggerPressed && !state.triggerPressedLastFrame) {
			if (state === controllerStates.rightController) {
				voltage = Math.min(0.4, voltage + 0.08);
			} else {
				voltage = Math.max(-1.4, voltage - 0.08);
			}
		}

		state.triggerPressedLastFrame = state.triggerPressed;
	});

	controllerStates.leftController.triggerPressedLastFrame = controllerStates.leftController.triggerPressed;
	controllerStates.rightController.triggerPressedLastFrame = controllerStates.rightController.triggerPressed;
}

function update() {
    renderer.setAnimationLoop( function(timestamp, frame) {        
        updateXRControllerStates(frame);

        var currentTime = performance.now();
        var time = clock.getDelta()/15;
        scene.remove(innerCube);
        // update inner box size based on formula using voltage
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
    
        //SCATTER (update velocities for scattering)
        scatter(currentTime); 

        addAcceleration(electronSpheres, innerBoxSize, time, -1);
        addAcceleration(holeSpheres, innerBoxSize, time, 1);

        //GENERATION ANIMATION
        Generation.generationAnim(holeSpheres, electronSpheres, generatedPairs, scene, boltz);

        //determines if distance of generated pair is far enough to allow recombinationn
        Recombination.updateRecombinationStatus(electronSpheres, holeSpheres, minDistance);
        //RECOMBINATION ANIMATION
        Recombination.recombinationAnim(electronSpheres, holeSpheres, innerBoxSize, scene, recombination_orbs);

        if (voltage < 0) {
            sphereCrossed(electronSpheres, 'e');
            sphereCrossed(holeSpheres, 'h');
        }

        if (voltage > 0) {
            console.log("recombination count when: " + Recombination.recombinationCount);
            if (Recombination.recombinationOccured && !batteryAdded) {
                // console.log("recombination occured");
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
                // console.log("length of pos array" + positiveBatteryElements.length);
            } else {
                batteryAdded = false;
                console.log("recombination check false, has not occurred yet");
            }
        }
        
        if (positiveBatteryElements.length > 0) { //if something exists in battery
            positive_battery_anim();
        }

        if (negativeBatteryElements.length > 0) {
            negative_battery_anim();
        }



        //UPDATE SPHERE POSITION
        updateSpherePosition();
        checkBounds(holeSpheres, electronSpheres, boxMin, boxMax);

         tickWristSlider(frame);                // <-- update wrist pose + drag
  voltage = getVoltageFromWristSlider(); // <-- use slider to drive the sim
  const vEl = document.getElementById('myText');
  if (vEl) vEl.textContent = voltage.toFixed(2);
setVoltageOnWristSlider(voltage);

		updateCamera();


        renderer.render( scene, camera );
		
    });
}
// Define buildController function
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
            material = new THREE.MeshBasicMaterial({ 
                opacity: 0.5, 
                transparent: true 
            });
            return new THREE.Mesh(geometry, material);
    }
}

function setUpVRControls() {
    // Create dolly for camera movement
    dolly = new THREE.Object3D();
    dolly.position.set(0, 0, 0);
    dolly.add(camera);
    scene.add(dolly);

    //controllers
    controller1 = renderer.xr.getController(0);
    controller2 = renderer.xr.getController(1);
    
    controller1.addEventListener('selectstart', onSelectStart);
    controller1.addEventListener('selectend', onSelectEnd);
    controller1.addEventListener('connected', function(event) {
        this.userData.inputSource = event.data;
        this.userData.isVisionPro = isVisionProInputSource(event.data);
        const visual = buildController(event.data);
        if (visual) {
            this.add(visual);
        }
    });
    controller1.addEventListener('disconnected', function() {
        this.userData.inputSource = null;
        this.userData.isVisionPro = false;
        while (this.children.length) {
            this.remove(this.children[0]);
        }
    });

    controller2.addEventListener('selectstart', onSelectStart);
    controller2.addEventListener('selectend', onSelectEnd);
    controller2.addEventListener('connected', function(event) {
        this.userData.inputSource = event.data;
        this.userData.isVisionPro = isVisionProInputSource(event.data);
        const visual = buildController(event.data);
        if (visual) {
            this.add(visual);
        }
    });
    controller2.addEventListener('disconnected', function() {
        this.userData.inputSource = null;
        this.userData.isVisionPro = false;
        while (this.children.length) {
            this.remove(this.children[0]);
        }
    });

    //controllerModelFactory
    const controllerModelFactory = new XRControllerModelFactory();
    
    //controllergrips
    controllerGrip1 = renderer.xr.getControllerGrip(0);
    controllerGrip2 = renderer.xr.getControllerGrip(1);
    
    controllerGrip1.add(controllerModelFactory.createControllerModel(controllerGrip1));
    controllerGrip2.add(controllerModelFactory.createControllerModel(controllerGrip2));
    
    
    // Add controllers to dolly
    dolly.add(controller1);
    dolly.add(controller2);
    dolly.add(controllerGrip1);
    dolly.add(controllerGrip2);
}

// Handle controller input
async function initXR(frame) {
    const xrSession = await navigator.xr.requestSession('immersive-vr');

    const inputSource = xrSession.inputSources[0];
	controllerGrip1 = xrSession.requestReferenceSpace('local');
}

function updateCamera() {
    if (!renderer.xr.isPresenting) return;

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
	const visionProActive = controllerStates.leftController.isVisionProSource || controllerStates.rightController.isVisionProSource;
	if (!visionProActive) {
		return;
	}

	const axesThreshold = 0.08;
	const hasActiveAxes = (Math.abs(controllerStates.leftController.thumbstick.x) > axesThreshold ||
		Math.abs(controllerStates.leftController.thumbstick.y) > axesThreshold ||
		Math.abs(controllerStates.rightController.thumbstick.x) > axesThreshold ||
		Math.abs(controllerStates.rightController.thumbstick.y) > axesThreshold);

	const controllersArray = [controller1, controller2];
	controllersArray.forEach(controller => {
		if (!controller || !controller.userData || !controller.userData.isSelecting) {
			return;
		}

		const inputSource = controller.userData.inputSource;
		if (!isVisionProInputSource(inputSource)) {
			return;
		}

		if (hasActiveAxes) {
			return; // Prefer trackpad-style input when axes are active
		}

		const direction = new THREE.Vector3();
		controller.getWorldDirection(direction);
		direction.negate(); // Controller rays point down -Z by default
		direction.y = 0;
		if (direction.lengthSq() < 1e-6) {
			return;
		}

		direction.normalize();
		dolly.position.addScaledVector(direction, vrSettings.moveSpeed * 0.5);
	});
}


// Add these controller event functions
function onSelectStart() {
    this.userData.isSelecting = true;
}

function onSelectEnd() {
    this.userData.isSelecting = false;
}











	
function negative_battery_anim() {
    for (var i = negativeBatteryElements.length - 1; i >= 0; i--) {
        var sphere = negativeBatteryElements[i];
        var spherePosition = sphere.object.position;
        if (sphere.value == 'e') {
            if (spherePosition.x <= cubeSize.x/2) {
                //move linear
                sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));

            } else {
                //fade out and remove from scene
                sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));

                sphere.object.material.transparent = true;

                // Update opacity based on elapsed time
                // Calculate the distance from the electron to the edge of the system
                var distanceFromEdge = Math.abs(sphere.object.position.x - cubeSize.x/2);
                var maxDistance = 50; // Define the maximum distance at which the electron becomes fully transparent
                var opacity = THREE.MathUtils.clamp(1 - (distanceFromEdge / maxDistance), 0, 1);
                
                sphere.object.material.opacity = opacity;

                if (opacity <= 0) {
                    // Remove the electron from the scene and battery array
                    scene.remove(sphere.object);
                    negativeBatteryElements.splice(i, 1);
                }
            }

        } else if (sphere.value == 'h') {
            if (spherePosition.x >= -cubeSize.x/2) {
                //move linear
                sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));
            } else {
                //fade out and remove from scene
                sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));

                sphere.object.material.transparent = true;

                // Update opacity based on elapsed time
                // Calculate the distance from the electron to the edge of the system
                var distanceFromEdge = Math.abs(sphere.object.position.x + cubeSize.x/2);
                var maxDistance = 50; // Define the maximum distance at which the electron becomes fully transparent
                var opacity = THREE.MathUtils.clamp(1 - (distanceFromEdge / maxDistance), 0, 1);
                
                sphere.object.material.opacity = opacity;

                if (opacity <= 0) {
                    // Remove the electron from the scene and battery array
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
                
                // Remove the electron from the battery array
                positiveBatteryElements.splice(i, 1);
            } else {
                sphere.object.position.add(new THREE.Vector3(-0.2, 0, 0));     
            }
                        
        } else if (sphere.value == 'h') { // hole
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
                
                // Remove the electron from the battery array
                positiveBatteryElements.splice(i, 1);
            } else {
                sphere.object.position.add(new THREE.Vector3(0.2, 0, 0));
            } 
        }
    }
    
}

//keeps track of the newly created electrons/holes after a sphere crosses to the other side
function sphereCrossed(typeArray, type) { 
    var e_count = 0;
    var h_count = 0;

    if (!voltageChangedOnce) {
        // e_count = electronSpheres.length;
        // h_count = holeSpheres.length;
        voltageChangedOnce = true;
    }
    for (var i = 0; i < typeArray.length; i++) {
        var spherePosition = typeArray[i].object.position.x;
        // added voltage > 0 check too since similar processes occuring for both
        if (voltage < 0) {
            //AZAD CODE
            if (type == 'e') {    
                if (spherePosition > innerBoxSize/2) {
                    e_count= e_count+1;
                    //takes out electrons if count exceeds 50 max
                    if (e_count > numSpheres) {
                        e_count= e_count-1;
                        //console.log('e_count=',e_count);
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
                    //removes holes if it exceeds max 50
                    if (h_count > numSpheres ) {
                            //console.log('h_count=',h_count);
                        h_count= h_count-1;    
                        var position = new THREE.Vector3(-cubeSize.x/2 + 5, 0, 0);
                        var hole = SphereUtil.createSphereAt(position, holeColor, false);
                        scene.add(hole.object);
                        hole.value = "h";
                        typeArray[i].crossed = true;
                        negativeBatteryElements.push(hole);

                        //remove last electron from the existing electronArray
                        var randomIndex = Math.floor(Math.random() * holeSpheres.length);
                        scene.remove(holeSpheres[randomIndex].object);
                        holeSpheres[randomIndex].object.geometry.dispose();
                        holeSpheres[randomIndex].object.material.dispose();
                        holeSpheres.splice(randomIndex, 1);
                    }
                }
            }
        }

        //AZAD CODE
        if (voltage === 0 ) {
            if (type == 'e') {
                if (spherePosition > innerBoxSize/2) {
                    e_count= e_count+1;
                    if (e_count > numSpheres ) {
                        e_count= e_count-1;
                        // console.log("removing electron because it reached above:" + numSpheres);
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
                            //console.log('h_count=',h_count);
                        h_count= h_count-1;    
                        // console.log("removing hole because it reached above:" + numSpheres);

                        //remove last electron from the existing electronArray
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
        // if position is within -Xn < X < 0
        if ((-innerBoxSize/2 < spherePosition && spherePosition < 0)) {
            // check if dividing by two is appropriate or not
            acc = new THREE.Vector3(-1.53*(innerBoxSize/2 + spherePosition), 0 , 0);
        }
    
        // is position is within 0 < X < Xn
        if ((0 < spherePosition && spherePosition < innerBoxSize/2)) {
            acc = new THREE.Vector3(-1.53*(innerBoxSize/2 - spherePosition), 0, 0);
        }
    
        // everywhere else -- -cubeSize.x/2 + 1 < X < -Xn || Xn < X < cubeSize.x/2 - 1
        if ((-cubeSize.x/2 + 1 < spherePosition && spherePosition < -innerBoxSize/2) || (innerBoxSize/2 < spherePosition && spherePosition < cubeSize.x/2 - 1) || (spherePosition == 0)) {
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
     // implement scatter movement
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
    // cube boundaries y and z for (var i = 0; i < )
    var yedge = (cubeSize.y/2);
    var ynedge = -(yedge);
    var zedge = (cubeSize.z/2);
    var znedge = -(zedge);

    for (var i = 0; i < sphere1.length; i++) {
        if (sphere1[i].object.position.x >= max) {
            sphere1[i].object.position.x = min + 1;
            // sphere1.velocity.multiplyScalar(-1);
        } else if(sphere1[i].object.position.x <= min){
            sphere1[i].object.position.x = THREE.MathUtils.randFloat(min + 1, min + 20);
            // sphere1.object.position.x = minX1 + 1;
            // sphere1.velocity.multiplyScalar(-1);
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
            // sphere2.velocity.multiplyScalar(-1);
        } else if(sphere2[i].object.position.x <= min){
            sphere2[i].object.position.x = max - 1;
            // sphere2.velocity.multiplyScalar(-1);
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

// Function to reset GUI controls
function resetGUI() {
    gui.__controllers.forEach(controller => controller.setValue(controller.initialValue));
}


function createIon(minx, maxx, color, ionType) {
    var capsuleLength = 3;
    var radius = 0.5;
    const geometry = new THREE.CapsuleGeometry(radius, capsuleLength);
    //negative shape
    if (ionType == "acceptor") {
        var material = new THREE.MeshBasicMaterial({color: color, transparent: true, opacity: 0.2});
        var acceptor = new THREE.Mesh(geometry, material);
        // acceptor.rotateX(Math.PI/2);
        acceptor.rotateZ(Math.PI/2);
        acceptor.position.set(
            THREE.MathUtils.randFloat(minx, maxx),
            THREE.MathUtils.randFloat(-cubeSize.y/2 + 1, cubeSize.y/2 - 1),
            THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1)
        );
        scene.add(acceptor);
    } else if (ionType == 'donor') { //positive shape
        //create second geometry for plus shape
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
    var headLength = innerBoxSize/4; //size of arrow head
    scene.remove(arrowNegative);
    arrowNegative = new THREE.ArrowHelper(new THREE.Vector3(-1, 0, 0), origin, length, hex, headLength);
    scene.add(arrowNegative);
}

function box( width, height, depth ) {

    width = width * 0.5,
    height = height * 0.5,
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

    geometry.setAttribute( 'position', new THREE.Float32BufferAttribute( position, 3 ) );

    return geometry;

}


function onWindowResize() {
    camera.aspect = container.clientWidth / container.clientHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(container.clientWidth, container.clientHeight, false);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2))
}
