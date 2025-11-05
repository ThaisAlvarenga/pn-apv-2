import * as THREE from 'https://unpkg.com/three@0.163.0/build/three.module.js'; 
//SPHEREUTIL 

//boltzmann distribution variables

// CHANGING ALL THIS FOR VELOCTIY TESTS
var minScalar = 0.0001;
var maxScalar = 3.0; 

export let scalar = 0.5;           // was: var scalar = 0.5

export function setScalar(v) {      
  // clamp for safety; tweak bounds if you like
  const clamped = Math.max(0.0001, Math.min(3.0, Number(v)));
  scalar = clamped;
}

export function getScalar() {       // new
  return scalar;
}

export function createSphere(i, minPos, maxPos, sphereColor, transparency, cubeSize) {
    var opacityVal = null;
    if (transparency) {
        opacityVal = 0.6;
    }
    var geometry;
    var material;
    geometry = new THREE.SphereGeometry(1, 32, 32);

    if (sphereColor === 0xFF3131) {
        material = new THREE.MeshBasicMaterial({ color: sphereColor, wireframe: true}); 
    } else {
        material = new THREE.MeshBasicMaterial({ color: sphereColor, transparent: transparency, opacity: opacityVal}); 
    }
    const sphere = new THREE.Mesh(geometry, material);

    // Random position within the cube as specified
    sphere.position.set(
    THREE.MathUtils.randFloat(minPos, maxPos),
    THREE.MathUtils.randFloat(-cubeSize.y/2 + 1, cubeSize.y/2 - 1),
    THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1)
    );
    return {object: sphere, material: material};
}

export function createSphereAt(position, sphereColor, transparency) {
    var opacityVal = null;
    var geometry;
    var material;
    if (transparency) {
        opacityVal = 0.6;
    }
    geometry = new THREE.SphereGeometry(1, 32, 32);

    if (sphereColor === 0xFF3131) {
        material = new THREE.MeshBasicMaterial({ color: sphereColor, wireframe: true}); 
    } else {
        material = new THREE.MeshBasicMaterial({ color: sphereColor, transparent: transparency, opacity: opacityVal}); 
    }
    const sphere = new THREE.Mesh(geometry, material);

    // Random position within the cube as specified
    sphere.position.set(position.x, position.y, position.z);
    return {object: sphere, material: material};
}

export function getBoltzVelocity(boltz) {
    var r = boltz[Math.floor(Math.random() * boltz.length)];
    var theta = Math.random() * Math.PI;
    var phi = Math.random() * (2*Math.PI);

    const x = r*Math.sin(theta)*Math.cos(phi);
    const y = r*Math.sin(theta)*Math.sin(phi);
    const z = r*Math.cos(theta);

    var randomVelocity = new THREE.Vector3(x, y, z).multiplyScalar(scalar);

    return randomVelocity;
}

