import * as THREE from 'https://unpkg.com/three@0.163.0/build/three.module.js'; 

export var recombinationOccured = false;

export var recombinationCount = 0;

export function updateRecombinationStatus(electronSpheres, holeSpheres, minDistance) {
    for (let electron of electronSpheres) {
        for (let hole of holeSpheres) {
            if (electron.initPos != undefined && hole.initPos != undefined) {
                let electronDistance = electron.object.position.distanceTo(electron.initPos);
                let holeDistance = hole.object.position.distanceTo(hole.initPos);

                if (electronDistance > minDistance && holeDistance > minDistance) {
                    electron.recombine = true;
                    hole.recombine = true;
                }
            }
        }
    }
}

export function recombinationAnim(electronSpheres, holeSpheres, innerBoxSize, scene, recombination_orbs) {
    const lerpSpeed = 0.01; // Adjust for faster/slower lerping
    const removalThreshold = 0.6; // When to consider spheres "recombined"
    const pauseDuration = 60; // Number of frames to pause (adjust as needed)
    

    // Check for collisions and initiate lerping
    let midpoint;
    for (let i = 0; i < electronSpheres.length; i++) {
        for (let j = 0; j < holeSpheres.length; j++) {
            if (!electronSpheres[i] || !holeSpheres[j]) continue;
            let e_sphere_outside_depletion_range = electronSpheres[i].object.position.x < -innerBoxSize/2 - 20 || electronSpheres[i].object.position.x > innerBoxSize/2 + 20;
            let h_sphere_outside_depletion_range = holeSpheres[j].object.position.x < -innerBoxSize/2 - 20|| holeSpheres[j].object.position.x > innerBoxSize/2 + 20;
            if (e_sphere_outside_depletion_range && h_sphere_outside_depletion_range) {
               
                if (checkCollision(electronSpheres[i], holeSpheres[j])) {
                    if (!electronSpheres[i].lerping && !holeSpheres[j].lerping) {
                        electronSpheres[i].lerping = true;
                        holeSpheres[j].lerping = true;
                        electronSpheres[i].lerpPartner = holeSpheres[j];
                        holeSpheres[j].lerpPartner = electronSpheres[i];
                        electronSpheres[i].pauseCounter = 0;
                        holeSpheres[j].pauseCounter = 0;
                        electronSpheres[i].lerpProgress = 0;
                        holeSpheres[j].lerpProgress = 0;
                        
                        // electronSpheres[i].object.material.color.set(new THREE.Color(0x05D9FF));
                        // holeSpheres[j].object.material.color.set(new THREE.Color(0xff9cb0));
                        // Set velocity to zero during pause
                        electronSpheres[i].velocity.set(0, 0, 0);
                        holeSpheres[j].velocity.set(0, 0, 0);

                        // Calculate and store midpoint for both spheres
                        midpoint = new THREE.Vector3().addVectors(electronSpheres[i].object.position, holeSpheres[j].object.position).multiplyScalar(0.5);
                        electronSpheres[i].targetPosition = midpoint.clone();
                        holeSpheres[j].targetPosition = midpoint.clone(); 
                    }
                }
            }
        }
    }

    // Handle pausing and lerping
    for (let sphere of [...electronSpheres, ...holeSpheres]) {
        sphere.processed = false;
        if (sphere.lerping && !sphere.processed) {
            sphere.processed = true; 
            sphere.orbCreated = false;

            if (sphere.pauseCounter < pauseDuration) {
                // Pausing phase
                sphere.pauseCounter++;
            } else {
                //when lerping, add an orb
               
                // Lerping phase
                sphere.lerpProgress += lerpSpeed;
            
                sphere.object.position.lerp(sphere.targetPosition, sphere.lerpProgress);
                
                // Check if lerping is complete
                
                // alright we only want to create the orb once, so only create if an orb does not exist
                if (sphere.lerpProgress <= .25 && !sphere.orb && !sphere.orbCreated) { // when lerping is 25% done, create an orb 
                    const orbGeo = new THREE.SphereGeometry(3, 32, 32);
                    const orbMaterial = new THREE.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.4});
                    const orbSphere = new THREE.Mesh(orbGeo, orbMaterial);
                    orbSphere.position.copy(sphere.targetPosition);
                    sphere.orb = orbSphere;        
                    sphere.orb.gradualVal = 3;
                    sphere.orbCreated = true;
                    scene.add(sphere.orb);
                    //every recombination orb created should be stored inside here. and anything left has not been removed. 
                    recombination_orbs.push(sphere.orb);
                }
                if (sphere.orb) {
                    // Update orb position and scale
                    sphere.orb.position.copy(sphere.targetPosition);
                    sphere.orb.scale.setScalar(sphere.orb.gradualVal);
                    sphere.orb.gradualVal -= 0.035;

                    sphere.orb.material.opacity = 0.3 / (1 + Math.exp(0.5 * (sphere.orb.gradualVal - 5)));

                    // if (sphere.orb.gradualVal <= 1) {
                    //     recombinationOrbRemove();
                    // } 
                    if (sphere.orb.material.opacity <= 0.1) {
                        //change colors once orb exists
                        sphere.object.material.color.set(new THREE.Color(0x05D9FF));
                        sphere.lerpPartner.object.material.color.set(new THREE.Color(0xff9cb0));
                        sphere.orb.material.opacity = 0;
                    }  else {
                    } 
                    

                } 

                if (sphere.lerpProgress >= removalThreshold) {
                    removeSpherePair(sphere, sphere.lerpPartner, scene, electronSpheres, holeSpheres);
                }
                
            }
        }
    }
}

export function setRecombinationStatus(status) {
    console.log("set recombination Status to:" + status);
    recombinationOccured = status;
}

export function checkCollision(electron, hole) {
    // collision check...
    // if two are created from generation then they can't recombine
    let distance = new THREE.Vector3().subVectors(electron.object.position, hole.object.position).length();
    let coll_dist = 20;
    if (electron.recombine && hole.recombine) {
        if (distance <= coll_dist) {
            return true;
        } else {
            return false;
        }
    }
}

export function recombinationOrbRemove(recombination_orbs, scene) {
    if (recombination_orbs.length > 0) {
        recombination_orbs = recombination_orbs.filter(orb => {
            scene.remove(orb);
            orb.geometry.dispose();
            orb.material.dispose();
            return false; // Exclude the orb from the new array
        });
    }  
}

// Helper function to remove a pair of spheres
function removeSpherePair(sphere1, sphere2, scene, electronSpheres, holeSpheres) {
    scene.remove(sphere1.object);
    scene.remove(sphere2.object);
    // electronSpheres = electronSpheres.filter(s => s !== sphere1 && s !== sphere2);
    // holeSpheres = holeSpheres.filter(s => s !== sphere1 && s !== sphere2);
    
    // Clean up THREE.js objects
    [sphere1, sphere2].forEach(sphere => {
        sphere.object.geometry.dispose();
        sphere.object.material.dispose();
    });

          // Splice them out in-place:
    const eIndex1 = electronSpheres.indexOf(sphere1);
    if (eIndex1 >= 0) electronSpheres.splice(eIndex1, 1);
    const eIndex2 = electronSpheres.indexOf(sphere2);
    if (eIndex2 >= 0) electronSpheres.splice(eIndex2, 1);

    const hIndex1 = holeSpheres.indexOf(sphere1);
    if (hIndex1 >= 0) holeSpheres.splice(hIndex1, 1);
    const hIndex2 = holeSpheres.indexOf(sphere2);
    if (hIndex2 >= 0) holeSpheres.splice(hIndex2, 1);
    
    recombinationOccured = true;
    recombinationCount++;
    console.log("removed a sphere pair and set reocombination Occurred to true");
}