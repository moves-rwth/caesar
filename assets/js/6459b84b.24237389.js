"use strict";(self.webpackChunkcaesar_website=self.webpackChunkcaesar_website||[]).push([[7868],{3905:(e,t,n)=>{n.d(t,{Zo:()=>u,kt:()=>f});var a=n(7294);function r(e,t,n){return t in e?Object.defineProperty(e,t,{value:n,enumerable:!0,configurable:!0,writable:!0}):e[t]=n,e}function l(e,t){var n=Object.keys(e);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);t&&(a=a.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),n.push.apply(n,a)}return n}function o(e){for(var t=1;t<arguments.length;t++){var n=null!=arguments[t]?arguments[t]:{};t%2?l(Object(n),!0).forEach((function(t){r(e,t,n[t])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(n)):l(Object(n)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(n,t))}))}return e}function i(e,t){if(null==e)return{};var n,a,r=function(e,t){if(null==e)return{};var n,a,r={},l=Object.keys(e);for(a=0;a<l.length;a++)n=l[a],t.indexOf(n)>=0||(r[n]=e[n]);return r}(e,t);if(Object.getOwnPropertySymbols){var l=Object.getOwnPropertySymbols(e);for(a=0;a<l.length;a++)n=l[a],t.indexOf(n)>=0||Object.prototype.propertyIsEnumerable.call(e,n)&&(r[n]=e[n])}return r}var s=a.createContext({}),c=function(e){var t=a.useContext(s),n=t;return e&&(n="function"==typeof e?e(t):o(o({},t),e)),n},u=function(e){var t=c(e.components);return a.createElement(s.Provider,{value:t},e.children)},d="mdxType",m={inlineCode:"code",wrapper:function(e){var t=e.children;return a.createElement(a.Fragment,{},t)}},p=a.forwardRef((function(e,t){var n=e.components,r=e.mdxType,l=e.originalType,s=e.parentName,u=i(e,["components","mdxType","originalType","parentName"]),d=c(n),p=r,f=d["".concat(s,".").concat(p)]||d[p]||m[p]||l;return n?a.createElement(f,o(o({ref:t},u),{},{components:n})):a.createElement(f,o({ref:t},u))}));function f(e,t){var n=arguments,r=t&&t.mdxType;if("string"==typeof e||r){var l=n.length,o=new Array(l);o[0]=p;var i={};for(var s in t)hasOwnProperty.call(t,s)&&(i[s]=t[s]);i.originalType=e,i[d]="string"==typeof e?e:r,o[1]=i;for(var c=2;c<l;c++)o[c]=n[c];return a.createElement.apply(null,o)}return a.createElement.apply(null,n)}p.displayName="MDXCreateElement"},3901:(e,t,n)=>{n.d(t,{Z:()=>o});var a=n(7294),r=n(3743);const l={tableOfContentsInline:"tableOfContentsInline_prmo"};function o(e){let{toc:t,minHeadingLevel:n,maxHeadingLevel:o}=e;return a.createElement("div",{className:l.tableOfContentsInline},a.createElement(r.Z,{toc:t,minHeadingLevel:n,maxHeadingLevel:o,className:"table-of-contents",linkClassName:null}))}},3743:(e,t,n)=>{n.d(t,{Z:()=>f});var a=n(7462),r=n(7294),l=n(6668);function o(e){const t=e.map((e=>({...e,parentIndex:-1,children:[]}))),n=Array(7).fill(-1);t.forEach(((e,t)=>{const a=n.slice(2,e.level);e.parentIndex=Math.max(...a),n[e.level]=t}));const a=[];return t.forEach((e=>{const{parentIndex:n,...r}=e;n>=0?t[n].children.push(r):a.push(r)})),a}function i(e){let{toc:t,minHeadingLevel:n,maxHeadingLevel:a}=e;return t.flatMap((e=>{const t=i({toc:e.children,minHeadingLevel:n,maxHeadingLevel:a});return function(e){return e.level>=n&&e.level<=a}(e)?[{...e,children:t}]:t}))}function s(e){const t=e.getBoundingClientRect();return t.top===t.bottom?s(e.parentNode):t}function c(e,t){let{anchorTopOffset:n}=t;const a=e.find((e=>s(e).top>=n));if(a){return function(e){return e.top>0&&e.bottom<window.innerHeight/2}(s(a))?a:e[e.indexOf(a)-1]??null}return e[e.length-1]??null}function u(){const e=(0,r.useRef)(0),{navbar:{hideOnScroll:t}}=(0,l.L)();return(0,r.useEffect)((()=>{e.current=t?0:document.querySelector(".navbar").clientHeight}),[t]),e}function d(e){const t=(0,r.useRef)(void 0),n=u();(0,r.useEffect)((()=>{if(!e)return()=>{};const{linkClassName:a,linkActiveClassName:r,minHeadingLevel:l,maxHeadingLevel:o}=e;function i(){const e=function(e){return Array.from(document.getElementsByClassName(e))}(a),i=function(e){let{minHeadingLevel:t,maxHeadingLevel:n}=e;const a=[];for(let r=t;r<=n;r+=1)a.push(`h${r}.anchor`);return Array.from(document.querySelectorAll(a.join()))}({minHeadingLevel:l,maxHeadingLevel:o}),s=c(i,{anchorTopOffset:n.current}),u=e.find((e=>s&&s.id===function(e){return decodeURIComponent(e.href.substring(e.href.indexOf("#")+1))}(e)));e.forEach((e=>{!function(e,n){n?(t.current&&t.current!==e&&t.current.classList.remove(r),e.classList.add(r),t.current=e):e.classList.remove(r)}(e,e===u)}))}return document.addEventListener("scroll",i),document.addEventListener("resize",i),i(),()=>{document.removeEventListener("scroll",i),document.removeEventListener("resize",i)}}),[e,n])}function m(e){let{toc:t,className:n,linkClassName:a,isChild:l}=e;return t.length?r.createElement("ul",{className:l?void 0:n},t.map((e=>r.createElement("li",{key:e.id},r.createElement("a",{href:`#${e.id}`,className:a??void 0,dangerouslySetInnerHTML:{__html:e.value}}),r.createElement(m,{isChild:!0,toc:e.children,className:n,linkClassName:a}))))):null}const p=r.memo(m);function f(e){let{toc:t,className:n="table-of-contents table-of-contents__left-border",linkClassName:s="table-of-contents__link",linkActiveClassName:c,minHeadingLevel:u,maxHeadingLevel:m,...f}=e;const g=(0,l.L)(),h=u??g.tableOfContents.minHeadingLevel,b=m??g.tableOfContents.maxHeadingLevel,v=function(e){let{toc:t,minHeadingLevel:n,maxHeadingLevel:a}=e;return(0,r.useMemo)((()=>i({toc:o(t),minHeadingLevel:n,maxHeadingLevel:a})),[t,n,a])}({toc:t,minHeadingLevel:h,maxHeadingLevel:b});return d((0,r.useMemo)((()=>{if(s&&c)return{linkClassName:s,linkActiveClassName:c,minHeadingLevel:h,maxHeadingLevel:b}}),[s,c,h,b])),r.createElement(p,(0,a.Z)({toc:v,className:n,linkClassName:s},f))}},5277:(e,t,n)=>{n.r(t),n.d(t,{assets:()=>H,contentTitle:()=>I,default:()=>j,frontMatter:()=>T,metadata:()=>D,toc:()=>S});var a=n(7462),r=n(7294),l=n(3905),o=n(614),i=n(9960),s=n(6010),c=n(2466),u=n(6550),d=n(1980),m=n(7392),p=n(12);function f(e){return function(e){return r.Children.map(e,(e=>{if(!e||(0,r.isValidElement)(e)&&function(e){const{props:t}=e;return!!t&&"object"==typeof t&&"value"in t}(e))return e;throw new Error(`Docusaurus error: Bad <Tabs> child <${"string"==typeof e.type?e.type:e.type.name}>: all children of the <Tabs> component should be <TabItem>, and every <TabItem> should have a unique "value" prop.`)}))?.filter(Boolean)??[]}(e).map((e=>{let{props:{value:t,label:n,attributes:a,default:r}}=e;return{value:t,label:n,attributes:a,default:r}}))}function g(e){const{values:t,children:n}=e;return(0,r.useMemo)((()=>{const e=t??f(n);return function(e){const t=(0,m.l)(e,((e,t)=>e.value===t.value));if(t.length>0)throw new Error(`Docusaurus error: Duplicate values "${t.map((e=>e.value)).join(", ")}" found in <Tabs>. Every value needs to be unique.`)}(e),e}),[t,n])}function h(e){let{value:t,tabValues:n}=e;return n.some((e=>e.value===t))}function b(e){let{queryString:t=!1,groupId:n}=e;const a=(0,u.k6)(),l=function(e){let{queryString:t=!1,groupId:n}=e;if("string"==typeof t)return t;if(!1===t)return null;if(!0===t&&!n)throw new Error('Docusaurus error: The <Tabs> component groupId prop is required if queryString=true, because this value is used as the search param name. You can also provide an explicit value such as queryString="my-search-param".');return n??null}({queryString:t,groupId:n});return[(0,d._X)(l),(0,r.useCallback)((e=>{if(!l)return;const t=new URLSearchParams(a.location.search);t.set(l,e),a.replace({...a.location,search:t.toString()})}),[l,a])]}function v(e){const{defaultValue:t,queryString:n=!1,groupId:a}=e,l=g(e),[o,i]=(0,r.useState)((()=>function(e){let{defaultValue:t,tabValues:n}=e;if(0===n.length)throw new Error("Docusaurus error: the <Tabs> component requires at least one <TabItem> children component");if(t){if(!h({value:t,tabValues:n}))throw new Error(`Docusaurus error: The <Tabs> has a defaultValue "${t}" but none of its children has the corresponding value. Available values are: ${n.map((e=>e.value)).join(", ")}. If you intend to show no default tab, use defaultValue={null} instead.`);return t}const a=n.find((e=>e.default))??n[0];if(!a)throw new Error("Unexpected error: 0 tabValues");return a.value}({defaultValue:t,tabValues:l}))),[s,c]=b({queryString:n,groupId:a}),[u,d]=function(e){let{groupId:t}=e;const n=function(e){return e?`docusaurus.tab.${e}`:null}(t),[a,l]=(0,p.Nk)(n);return[a,(0,r.useCallback)((e=>{n&&l.set(e)}),[n,l])]}({groupId:a}),m=(()=>{const e=s??u;return h({value:e,tabValues:l})?e:null})();(0,r.useLayoutEffect)((()=>{m&&i(m)}),[m]);return{selectedValue:o,selectValue:(0,r.useCallback)((e=>{if(!h({value:e,tabValues:l}))throw new Error(`Can't select invalid tab value=${e}`);i(e),c(e),d(e)}),[c,d,l]),tabValues:l}}var k=n(2389);const y={tabList:"tabList__CuJ",tabItem:"tabItem_LNqP"};function w(e){let{className:t,block:n,selectedValue:l,selectValue:o,tabValues:i}=e;const u=[],{blockElementScrollPositionUntilNextRender:d}=(0,c.o5)(),m=e=>{const t=e.currentTarget,n=u.indexOf(t),a=i[n].value;a!==l&&(d(t),o(a))},p=e=>{let t=null;switch(e.key){case"Enter":m(e);break;case"ArrowRight":{const n=u.indexOf(e.currentTarget)+1;t=u[n]??u[0];break}case"ArrowLeft":{const n=u.indexOf(e.currentTarget)-1;t=u[n]??u[u.length-1];break}}t?.focus()};return r.createElement("ul",{role:"tablist","aria-orientation":"horizontal",className:(0,s.Z)("tabs",{"tabs--block":n},t)},i.map((e=>{let{value:t,label:n,attributes:o}=e;return r.createElement("li",(0,a.Z)({role:"tab",tabIndex:l===t?0:-1,"aria-selected":l===t,key:t,ref:e=>u.push(e),onKeyDown:p,onClick:m},o,{className:(0,s.Z)("tabs__item",y.tabItem,o?.className,{"tabs__item--active":l===t})}),n??t)})))}function C(e){let{lazy:t,children:n,selectedValue:a}=e;const l=(Array.isArray(n)?n:[n]).filter(Boolean);if(t){const e=l.find((e=>e.props.value===a));return e?(0,r.cloneElement)(e,{className:"margin-top--md"}):null}return r.createElement("div",{className:"margin-top--md"},l.map(((e,t)=>(0,r.cloneElement)(e,{key:t,hidden:e.props.value!==a}))))}function N(e){const t=v(e);return r.createElement("div",{className:(0,s.Z)("tabs-container",y.tabList)},r.createElement(w,(0,a.Z)({},e,t)),r.createElement(C,(0,a.Z)({},e,t)))}function L(e){const t=(0,k.Z)();return r.createElement(N,(0,a.Z)({key:String(t)},e))}const x={tabItem:"tabItem_Ymn6"};function E(e){let{children:t,hidden:n,className:a}=e;return r.createElement("div",{role:"tabpanel",className:(0,s.Z)(x.tabItem,a),hidden:n},t)}var O=n(3901);const T={description:"You can install Caesar locally or build a Docker image.",sidebar_position:1},I="Installing Caesar",D={unversionedId:"getting-started/installation",id:"getting-started/installation",title:"Installing Caesar",description:"You can install Caesar locally or build a Docker image.",source:"@site/docs/getting-started/installation.mdx",sourceDirName:"getting-started",slug:"/getting-started/installation",permalink:"/docs/getting-started/installation",draft:!1,editUrl:"https://github.com/moves-rwth/caesar/tree/main/website/docs/getting-started/installation.mdx",tags:[],version:"current",sidebarPosition:1,frontMatter:{description:"You can install Caesar locally or build a Docker image.",sidebar_position:1},sidebar:"docsSidebar",previous:{title:"Getting Started",permalink:"/docs/getting-started/"},next:{title:"Guide to HeyVL",permalink:"/docs/getting-started/heyvl-guide"}},H={},S=[{value:"Option A: Compiling Locally (Recommended)",id:"option-a-compiling-locally-recommended",level:2},{value:"Installing Dependencies",id:"installing-dependencies",level:3},{value:"Compiling Caesar",id:"compiling-caesar",level:3},{value:"Option B: Docker",id:"option-b-docker",level:2}],V={toc:S},Z="wrapper";function j(e){let{components:t,...n}=e;return(0,l.kt)(Z,(0,a.Z)({},V,n,{components:t,mdxType:"MDXLayout"}),(0,l.kt)("h1",{id:"installing-caesar"},"Installing Caesar"),(0,l.kt)("p",null,"You can install Caesar locally or build a Docker image."),(0,l.kt)(O.Z,{toc:S,mdxType:"TOCInline"}),(0,l.kt)("h2",{id:"option-a-compiling-locally-recommended"},"Option A: Compiling Locally (Recommended)"),(0,l.kt)("h3",{id:"installing-dependencies"},"Installing Dependencies"),(0,l.kt)("p",null,"You will need to install some dependencies manually:"),(0,l.kt)("p",null,(0,l.kt)("strong",{parentName:"p"},"Rust:")," To install ",(0,l.kt)("a",{parentName:"p",href:"https://www.rust-lang.org/"},"Rust"),", we recommend ",(0,l.kt)("a",{parentName:"p",href:"https://rustup.rs/"},"installation via rustup"),"."),(0,l.kt)("p",null,(0,l.kt)("strong",{parentName:"p"},"Fish Shell"),": We write some scripts written in ",(0,l.kt)("a",{parentName:"p",href:"https://fishshell.com/"},"fish"),"."),(0,l.kt)("p",null,(0,l.kt)("strong",{parentName:"p"},"Build Tools:")," Caesar builds ",(0,l.kt)("a",{parentName:"p",href:"https://github.com/Z3Prover/z3"},"Z3")," itself, so we need Python and ",(0,l.kt)("a",{parentName:"p",href:"https://cmake.org/"},"cmake"),"."),(0,l.kt)(L,{groupId:"operating-systems",mdxType:"Tabs"},(0,l.kt)(E,{value:"mac",label:"macOS",mdxType:"TabItem"},(0,l.kt)(o.Z,{language:"bash",mdxType:"CodeBlock"},"# Install Rust via rustup\ncurl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh\n# Install CMake and fish\nbrew install cmake fish")),(0,l.kt)(E,{value:"debian",label:"Debian/Linux",mdxType:"TabItem"},(0,l.kt)(o.Z,{language:"bash",mdxType:"CodeBlock"},"# Install Rust via rustup\ncurl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh\n# Install CMake, LLVM, clang, and fish\napt-get install cmake llvm libclang clang fish")),(0,l.kt)(E,{value:"win",label:"Windows",mdxType:"TabItem"},"We do not have build instructions for Windows at the moment. We recommend that you use ",(0,l.kt)(i.Z,{to:"https://learn.microsoft.com/en-us/windows/wsl/install",mdxType:"Link"},"WSL")," and refer to the Debian/Linux instructions.")),(0,l.kt)("h3",{id:"compiling-caesar"},"Compiling Caesar"),(0,l.kt)("p",null,"Simply run the following, and ",(0,l.kt)("inlineCode",{parentName:"p"},"caesar")," will be available on the command-line.\nBecause this will compile a large number of dependencies, this might take a couple of minutes (especially Z3 takes some time)."),(0,l.kt)("pre",null,(0,l.kt)("code",{parentName:"pre",className:"language-bash"},"git clone git@github.com:moves-rwth/caesar.git\ncd caesar\ncargo install --path . caesar\n")),(0,l.kt)("p",null,"Then, you can run an example:"),(0,l.kt)("pre",null,(0,l.kt)("code",{parentName:"pre",className:"language-bash"},"caesar tests/zeroconf.heyvl \n")),(0,l.kt)("p",null,"And this will print:"),(0,l.kt)("pre",null,(0,l.kt)("code",{parentName:"pre"},"tests/zeroconf.heyvl::arp: Verified.\ntests/zeroconf.heyvl::zeroconf: Verified.\n")),(0,l.kt)("h2",{id:"option-b-docker"},"Option B: Docker"),(0,l.kt)("p",null,"We also support building a Docker image.\nThis does not require installing dependencies and will package everything in a Docker image named ",(0,l.kt)("inlineCode",{parentName:"p"},"caesar"),"."),(0,l.kt)("pre",null,(0,l.kt)("code",{parentName:"pre",className:"language-bash"},"git clone git@github.com:moves-rwth/caesar.git\ncd caesar\ndocker build -t caesar -f docker/Dockerfile .\n")),(0,l.kt)("p",null,"With the Docker image ",(0,l.kt)("inlineCode",{parentName:"p"},"caesar")," built, you can enter the Docker container and work in there.\nThe following command also mounts the ",(0,l.kt)("inlineCode",{parentName:"p"},"./caesar/")," directory as ",(0,l.kt)("inlineCode",{parentName:"p"},"/root/caesar/results/")," inside the container."),(0,l.kt)("pre",null,(0,l.kt)("code",{parentName:"pre",className:"language-bash"},"docker run -it -v $PWD/results:/root/caesar/results/ caesar /bin/bash\n")))}j.isMDXComponent=!0}}]);