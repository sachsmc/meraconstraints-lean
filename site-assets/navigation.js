// A shared navigation bar, valid under a GitHub Pages project subpath too.
(() => {
  const script = document.currentScript;
  if (!script) return;
  const root = new URL("./", script.src);
  const addNavigation = () => {
    if (document.getElementById("project-navigation")) return;
    if (location.pathname.startsWith(new URL("docs/",root).pathname)) document.body.classList.add("mera-api");
    const nav = document.createElement("nav");
    nav.id = "project-navigation";
    nav.setAttribute("aria-label", "Project documentation");
    for (const [label, path] of [
      ["MERA constraints · Lean 4", ""], ["Book", ""], ["Reading guide", "guide/"],
      ["Scope & assumptions", "scope/"], ["API", "docs/"], ["Resources", "resources/"]
    ]) {
      const link = document.createElement("a");
      link.textContent = label;
      link.href = new URL(path, root).href;
      nav.append(link);
    }
    document.body.prepend(nav);
    const measure = () => document.body.style.setProperty("--project-navigation-height", `${nav.getBoundingClientRect().height}px`);
    measure();
    new ResizeObserver(measure).observe(nav);
  };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", addNavigation);
  else addNavigation();
})();
