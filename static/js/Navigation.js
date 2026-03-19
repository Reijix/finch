/*
This module uses the HTML5 History API (https://developer.mozilla.org/en-US/docs/Web/API/History_API)
to implement buttons for forward and backward navigation.

We store an index into the history and we store the maximum index of the history in sessionStorage
(https://developer.mozilla.org/en-US/docs/Web/API/Window/sessionStorage).
*/

// Init the state / fetch it, if session storage exists.
let currentIndex = 0;
let maxIndex = sessionStorage.getItem("maxIndex")
  ? parseInt(sessionStorage.getItem("maxIndex"))
  : 0;

// Initialize the history tracking, this should be called after setup of the app.
function initHistory(url) {
  // Check if the current history state already has an index (e.g., after a page reload)
  if (window.history.state && window.history.state.index !== undefined) {
    currentIndex = window.history.state.index;
  } else {
    // otherwise set defaults
    currentIndex = 0;
    maxIndex = 0;
    sessionStorage.setItem("maxIndex", maxIndex);
  }
  window.history.replaceState({ index: currentIndex }, "", url);
  updateButtonStates();
}

// Wrapper for pushState (https://developer.mozilla.org/en-US/docs/Web/API/History/pushState),
// which also updates our history index, and stores the index as history state.
function pushStateHistory(url) {
  currentIndex++;
  maxIndex = currentIndex; // Pushing a new state invalidates future forward history
  sessionStorage.setItem("maxIndex", maxIndex);
  window.history.pushState({ index: currentIndex }, "", url);
  updateButtonStates();
}

// Event listener for 'popstate', which is called whenever navigation is used (forward/backward).
// Grabs the index of the previous (or future) state.
window.addEventListener("popstate", (event) => {
  if (event.state && event.state.index !== undefined) {
    currentIndex = event.state.index;
  } else {
    // Fallback if somehow no state exists.
    currentIndex = 0;
  }
  updateButtonStates();
});

// Disables the navigation buttons if no history exists.
function updateButtonStates() {
  const backBtn = document.getElementById("back-button");
  const fwdBtn = document.getElementById("forward-button");

  if (backBtn) {
    backBtn.disabled = currentIndex <= 0;
  }

  if (fwdBtn) {
    fwdBtn.disabled = currentIndex >= maxIndex;
  }
}
