import * as THREE from 'https://unpkg.com/three@0.163.0/build/three.module.js'; 
import * as SphereUtil from './sphere.js';
import { ImprovedNoise } from 'https://unpkg.com/three@0.163.0/examples/jsm/math/ImprovedNoise.js';


// in the viz

// positive is red
// negative is blue
// generaition is when they 
// the recombination is when they fuse and disappear

// movement 
// scattering -> after a certain amount of time they change direction

// the box is called depletion and it's the elective field
// arrow point with an E is the electriv field and its direction

var minScalar = 0.22;
var maxScalar = 0.88;
var scatterTimeMean = 2;
const perlin = new ImprovedNoise();
var numSpheres = 50;

// positive
var holeColor = 0xd55e00
// negative charge
var electronColor = 0x56b4e9;



export function generationAnim(holeSpheres, electronSpheres, generatedPairs, scene, boltz) {
    // if a generated pair exists
    let maxOrbSize = 6;
    if (generatedPairs.length > 0) {
        let index = 0;
        //iterate through generatedPair array and animate the pair
        //after pair moves away from each other, alter orb opacity until 
        //conditions have been met, add pair to respective electron and hole array
        //and remove green orb from scene
        for (let pair of generatedPairs) {
            let hole = pair.hole;
            let electron = pair.electron;
            let orb = pair.orbSphere;
            if (orb.gradualVal <= maxOrbSize && orb.material.opacity > 0) {
                hole.object.position.add(hole.velocity);
                electron.object.position.add(electron.velocity);
                let opacityFactor = Math.max(0, 1 - (orb.gradualVal - 1) / (maxOrbSize - 1));
                orb.material.opacity = opacityFactor;
                orb.gradualVal += 0.1;
            } else {
                scene.remove(orb);
                generatedPairs.splice(index, 1);
                holeSpheres.push({
                    value: "h", 
                    initPos: pair.position.clone().add(new THREE.Vector3(2,0,0)), 
                    crossReady: false, 
                    crossed: false, 
                    pause: false, 
                    lerpProgress: 0, 
                    lerping: false, 
                    lerpPartner: new THREE.Vector3(), 
                    id: "generated", 
                    recombine: false, 
                    canMove: true, 
                    object: hole.object, 
                    material: hole.material, 
                    velocity: SphereUtil.getBoltzVelocity(boltz),
                    speed: Math.random() * (maxScalar - minScalar + 1) + minScalar, 
                    scatterStartTime: performance.now(), 
                    scatterTime: (scatterTimeMean + (perlin.noise(Math.random(0, numSpheres) * 100, Math.random(0, numSpheres) * 200, performance.now() * 0.001) - 0.5)*0.3)});
    
                    electronSpheres.push({
                        value: "e", 
                        initPos: pair.position.clone(), 
                        crossReady: false, 
                        crossed: false, 
                        pause: false, 
                        lerpProgress: 0, 
                        lerping: false, 
                        lerpPartner: new THREE.Vector3(), 
                        id: "generated", 
                        recombine: false, 
                        canMove: true, 
                        object: electron.object, 
                        material: electron.material, 
                        velocity: SphereUtil.getBoltzVelocity(boltz),
                        speed: Math.random() * (maxScalar - minScalar + 1) + minScalar, 
                        scatterStartTime: performance.now(), 
                        scatterTime: (scatterTimeMean + (perlin.noise(Math.random(0, numSpheres) * 100, Math.random(0, numSpheres) * 200, performance.now() * 0.001) - 0.5)*0.3)
                    });    
            }
            index++;
        }
    }
}

export function generatePair(cubeSize) {
    let position = new THREE.Vector3(
        THREE.MathUtils.randFloat(-cubeSize.x/2 + 1, cubeSize.x/2 - 1), 
        THREE.MathUtils.randFloat(-cubeSize.y/2 + 1, cubeSize.y/2 - 1), 
        THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1));
    // holes and electron are created at the same position
    let hole = SphereUtil.createSphereAt(position.clone().add(new THREE.Vector3(2,0,0)), holeColor, false);
    let electron = SphereUtil.createSphereAt(position.clone(), electronColor, false);
    
    //set initial generation values to hole and electrons
    hole.velocity = new THREE.Vector3(-0.02, 0, 0);
    electron.velocity =  new THREE.Vector3(0.02, 0, 0);

    //generate orb
    const orbGeo = new THREE.SphereGeometry(2, 32, 32);
    const orbMaterial = new THREE.MeshBasicMaterial({ color: 0x009e73, transparent: true, opacity: 0.5});
    const orbSphere = new THREE.Mesh(orbGeo, orbMaterial);
    
    //calculate orb position using midpoint of pair and set position
    let midpoint = hole.object.position.clone().add(electron.object.position.clone()).multiplyScalar(0.5);
    orbSphere.position.copy(midpoint);
    //initial orb opacity level
    orbSphere.gradualVal = 0.5;

    //generatedPair array [{hole, electron, orbSphere, position}]
    return {hole, electron, orbSphere, position};
}

export function solarGeneratePair(solarCell, trapezoid_top, trapezoid_height, cubeSize) {
    let position = new THREE.Vector3(
        THREE.MathUtils.randFloat(-trapezoid_top/2 + (solarCell.position.x), trapezoid_top/2 + (solarCell.position.x)), 
        THREE.MathUtils.randFloat(-trapezoid_height/2, trapezoid_height/2), 
        THREE.MathUtils.randFloat(-cubeSize.z/2 + 1, cubeSize.z/2 - 1));
    
    if (position.x < -cubeSize.x / 2 + 1 || position.x > cubeSize.x / 2 - 1 || position.y > cubeSize.y/2 - 1 || position.y < -cubeSize.y/2 + 1) {
        position.x = THREE.MathUtils.clamp(position.x, -cubeSize.x / 2 + 1, cubeSize.x / 2 - 1);
        position.y = THREE.MathUtils.clamp(position.y, -cubeSize.x / 2 + 1, cubeSize.x / 2 - 1);
    }

     // holes and electron are created at the same position
     let hole = SphereUtil.createSphereAt(position.clone().add(new THREE.Vector3(2,0,0)), holeColor, false);
     let electron = SphereUtil.createSphereAt(position.clone(), electronColor, false);
     
     // set initial generation values to hole and electrons
     hole.velocity = new THREE.Vector3(-0.02, 0, 0);
     electron.velocity =  new THREE.Vector3(0.02, 0, 0);
 
     // generate orb
     const orbGeo = new THREE.SphereGeometry(2, 32, 32);
     const orbMaterial = new THREE.MeshBasicMaterial({ color: 0x009e73, transparent: true, opacity: 0.5});
     const orbSphere = new THREE.Mesh(orbGeo, orbMaterial);
     
     // calculate orb position using midpoint of pair and set position
     let midpoint = hole.object.position.clone().add(electron.object.position.clone()).multiplyScalar(0.5);
     orbSphere.position.copy(midpoint);
     // initial orb opacity level
     orbSphere.gradualVal = 0.5;
     
 
     // generatedPair array [{hole, electron, orbSphere, position}]
     return {hole, electron, orbSphere, position};                
}

